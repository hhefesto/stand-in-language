{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Generic terminal ABI and core evaluator agreement runner.
module Telomare.Machine
  ( TextU
  , ReplyU
  , CoreEntry (..)
  , Program (..)
  , programCertificateSummary
  , programDepth
  , runProgramScript
  , runProgramIO
  ) where

import Control.Monad (when)
import Data.Char (chr, ord)
import Data.Maybe (fromMaybe)
import Data.Type.Equality ((:~:) (Refl))
import Numeric.Natural (Natural)
import System.IO (hFlush, hPutStrLn, isEOF, stderr, stdout)

import Telomare.Budget (costW, shapeOfSTy)
import Telomare.Compiler.Direct (Strip, eraseMorph, stripSTy)
import Telomare.Core
import Telomare.Denotation
import Telomare.Surface

type TextU = 'UList 'UNat
type ReplyU s = TextU ':**: ('UUnit ':++: s)

-- | A compiled entry may end at a decorated core object. Its erasure must be
-- exactly the source result; the host never inserts a box coercion.
data CoreEntry a b where
  CoreEntry
    :: SUTy a
    -> STy c
    -> (Strip c :~: b)
    -> Morph (Lift a) c
    -> CoreEntry a b

-- | The source chooses @s@. The host retains only its witness and the two
-- compiled entry morphisms required by the terminal protocol.
data Program where
  Program
    :: SUTy s
    -> UMorph 'UUnit (ReplyU s)
    -> UMorph (TextU ':**: s) (ReplyU s)
    -> CoreEntry 'UUnit (ReplyU s)
    -> CoreEntry (TextU ':**: s) (ReplyU s)
    -> Program

programCertificateSummary :: Program -> String
programCertificateSummary program@(Program stateTy _ _ initial step) =
  "typed affine program: core depth " <> show (programDepth program)
    <> "\nstatic work bound: init " <> boundOf initial
    <> ", step " <> boundOf step <> " (any input)"
  where
    boundOf :: CoreEntry a b -> String
    boundOf (CoreEntry inputTy _ _ morph) =
      case fst (costW morph (shapeOfSTy inputTy)) of
        Just n  -> "<= " <> show n
        Nothing -> "unbounded (contains unsized recursion)"

programDepth :: Program -> Natural
programDepth (Program _ _ _ initial step) = max (entryDepth initial) (entryDepth step)
  where
    entryDepth (CoreEntry _ _ _ morph) = depth morph

runProgramScript :: Program -> [String] -> Either String (String, Natural)
runProgramScript (Program stateTy initialU stepU initial step) inputs = do
  (reply, initialWork) <- runCore replyTy initial ()
  if not (equalU replyTy (evalU initialU ()) reply)
    then Left "surface/core evaluator disagreement"
    else do
      output <- decode (fst reply)
      go replyTy inputTy stepU step output initialWork (snd reply) inputs
  where
    replyTy = SUProd (SUList SUNat) (SUSum SUUnit stateTy)
    inputTy = SUProd (SUList SUNat) stateTy
    go _ _ _ _ transcript total (Left ()) _ = Right (transcript, total)
    go rt it source core transcript total (Right state) (input : rest) = do
      let inputValue = (encode input, state)
      (reply, spent) <- runCore rt core inputValue
      if not (equalU rt (evalU source inputValue) reply)
        then Left "surface/core evaluator disagreement"
        else do
          output <- decode (fst reply)
          go rt it source core (transcript <> output) (total + spent) (snd reply) rest
    go _ _ _ _ transcript total (Right _) [] = Right (transcript, total)

runProgramIO :: Maybe Natural -> Bool -> Program -> IO (Either String ())
runProgramIO limit report (Program stateTy sourceInit sourceStep initial step) = do
  result <- runInteractive replyTy limit 0 initial ()
  case result of
    Left err -> pure (Left err)
    Right (reply, remaining, spent)
      | not (equalU replyTy (evalU sourceInit ()) reply) ->
          pure (Left "surface/core evaluator disagreement")
      | otherwise -> loop remaining spent (0 :: Natural) reply
  where
    replyTy = SUProd (SUList SUNat) (SUSum SUUnit stateTy)
    loop remaining spent count (output, continuation) = do
      case decode output of
        Left err -> pure (Left err)
        Right rendered -> do
          putStr rendered
          hFlush stdout
          case continuation of
            Left () -> finish spent count
            Right state -> do
              eof <- isEOF
              if eof then finish spent count else do
                input <- getLine
                let inputValue = (encode input, state)
                result <- runInteractive replyTy remaining spent step inputValue
                case result of
                  Left err -> pure (Left err)
                  Right (reply, remaining', spent')
                    | not (equalU replyTy (evalU sourceStep inputValue) reply) ->
                        pure (Left "surface/core evaluator disagreement")
                    | otherwise -> loop remaining' spent' (count + 1) reply
    entryBound :: CoreEntry a b -> Maybe Natural
    entryBound (CoreEntry inputTy _ _ morph) =
      fst (costW morph (shapeOfSTy inputTy))
    finish spent count = do
      when report (hPutStrLn stderr ("core work: " <> show spent <> cap))
      pure (Right ())
      where
        -- the measured/certified bridge, with the arithmetic shown:
        -- a count-input session is certified to cost at most
        -- init-bound + count * step-bound, the numbers --certificate
        -- prints per entry
        cap = case (entryBound initial, entryBound step) of
          (Just ib, Just sb) ->
            " <= certified cap init " <> show ib <> " + "
              <> show count <> " steps * " <> show sb <> " = "
              <> show (ib + count * sb)
          _ -> ""

runCore :: SUTy b -> CoreEntry a b -> UVal a -> Either String (UVal b, Natural)
runCore _ (CoreEntry inputTy coreTy Refl morph) input =
  let liftedInput = toLift inputTy input
      value = evalV morph liftedInput
      (spent, gradedValue) = evalG workAlg morph liftedInput
  in case evalK morph liftedInput spent of
       Just (executed, 0)
         | equalCore coreTy value gradedValue
             && equalCore coreTy value executed ->
             Right (fromCore coreTy value, spent)
       _ -> Left "core evaluator disagreement"

runInteractive
  :: SUTy b
  -> Maybe Natural
  -> Natural
  -> CoreEntry a b
  -> UVal a
  -> IO (Either String (UVal b, Maybe Natural, Natural))
runInteractive _ limit already (CoreEntry inputTy coreTy Refl morph) input = pure $ do
  let liftedInput = toLift inputTy input
      value = evalV morph liftedInput
      (needed, gradedValue) = evalG workAlg morph liftedInput
      available = fromMaybe needed limit
  if available < needed
    then Left "core fuel exhausted"
    else case evalK morph liftedInput available of
      Just (executed, remaining)
        | equalCore coreTy value gradedValue
            && equalCore coreTy value executed ->
            Right (fromCore coreTy value, fmap (const remaining) limit, already + needed)
      _ -> Left "core evaluator disagreement"

equalU :: SUTy a -> UVal a -> UVal a -> Bool
equalU SUUnit _ _ = True
equalU SUNat a b = a == b
equalU (SUProd a b) (x, y) (x', y') = equalU a x x' && equalU b y y'
equalU (SUSum a _) (Left x) (Left y) = equalU a x y
equalU (SUSum _ b) (Right x) (Right y) = equalU b x y
equalU (SUSum _ _) _ _ = False
equalU (SUList a) xs ys = length xs == length ys && and (zipWith (equalU a) xs ys)
equalU (SULolly _ _) (UClosure sc1 b1 e1) (UClosure sc2 b2 e2) =
  -- conservative structural closure equality: same environment type,
  -- same body shape, equal environments
  case sameSUTy sc1 sc2 of
    Just Refl -> shapeU b1 == shapeU b2 && equalU sc1 e1 e2
    Nothing   -> False

equalCore :: STy a -> Val a -> Val a -> Bool
equalCore SUnit _ _ = True
equalCore SNat a b = a == b
equalCore (SProd a b) (x, y) (x', y') =
  equalCore a x x' && equalCore b y y'
equalCore (SSum a _) (Left x) (Left y) = equalCore a x y
equalCore (SSum _ b) (Right x) (Right y) = equalCore b x y
equalCore (SSum _ _) _ _ = False
equalCore (SList a) xs ys =
  length xs == length ys && and (zipWith (equalCore a) xs ys)
equalCore (SBang a) x y = equalCore a x y
equalCore (SLolly _ _) (Closure sc1 b1 e1) (Closure sc2 b2 e2) =
  case sameSTy sc1 sc2 of
    Just Refl -> shapeU (eraseMorph b1) == shapeU (eraseMorph b2)
                   && equalCore sc1 e1 e2
    Nothing   -> False

toLift :: SUTy a -> UVal a -> Val (Lift a)
toLift SUUnit x              = x
toLift SUNat x               = x
toLift (SUProd a b) (x, y)   = (toLift a x, toLift b y)
toLift (SUSum a _) (Left x)  = Left (toLift a x)
toLift (SUSum _ b) (Right x) = Right (toLift b x)
toLift (SUList a) xs         = fmap (toLift a) xs
toLift (SULolly _ _) _       =
  -- machine State/Reply are checked first-order at compile time
  -- (Telomare.Tel2), so this branch is unreachable from any program
  error "toLift: closures cannot cross the machine boundary"

fromCore :: STy a -> Val a -> UVal (Strip a)
fromCore SUnit x              = x
fromCore SNat x               = x
fromCore (SProd a b) (x, y)   = (fromCore a x, fromCore b y)
fromCore (SSum a _) (Left x)  = Left (fromCore a x)
fromCore (SSum _ b) (Right x) = Right (fromCore b x)
fromCore (SList a) xs         = fmap (fromCore a) xs
fromCore (SBang a) x          = fromCore a x
fromCore (SLolly _ _) (Closure sc body env) =
  UClosure (stripSTy sc) (eraseMorph body) (fromCore sc env)

encode :: String -> [Natural]
encode = fmap (fromIntegral . ord)

decode :: [Natural] -> Either String String
decode = traverse decodeChar
  where
    decodeChar n
      | n > 0x10ffff = Left ("invalid Unicode scalar value " <> show n)
      | n >= 0xd800 && n <= 0xdfff = Left ("invalid Unicode surrogate " <> show n)
      | otherwise = Right (chr (fromIntegral n))
