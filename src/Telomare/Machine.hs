{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

-- | Generic terminal ABI and core evaluator agreement runner.
module Telomare.Machine
  ( TextU
  , ReplyU
  , Program (..)
  , programDepth
  , runProgramScript
  , runProgramIO
  ) where

import Control.Monad (when)
import Data.Char (chr, ord)
import Data.Maybe (fromMaybe)
import Numeric.Natural (Natural)
import System.IO (hFlush, hPutStrLn, isEOF, stderr, stdout)

import Telomare.Core
import Telomare.Denotation
import Telomare.Surface

type TextU = 'UList 'UNat
type ReplyU s = TextU ':**: ('UUnit ':++: s)

-- | The source chooses @s@. The host retains only its witness and the two
-- compiled entry morphisms required by the terminal protocol.
data Program where
  Program
    :: SUTy s
    -> UMorph 'UUnit (ReplyU s)
    -> UMorph (TextU ':**: s) (ReplyU s)
    -> Morph 'Unit (Lift (ReplyU s))
    -> Morph (Lift (TextU ':**: s)) (Lift (ReplyU s))
    -> Program

programDepth :: Program -> Natural
programDepth (Program _ _ _ initial step) = max (depth initial) (depth step)

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
      (reply, spent) <- runCore rt core (toLift it inputValue)
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
      | otherwise -> loop remaining spent reply
  where
    replyTy = SUProd (SUList SUNat) (SUSum SUUnit stateTy)
    loop remaining spent (output, continuation) = do
      case decode output of
        Left err -> pure (Left err)
        Right rendered -> do
          putStr rendered
          hFlush stdout
          case continuation of
            Left () -> finish spent
            Right state -> do
              eof <- isEOF
              if eof then finish spent else do
                input <- getLine
                let inputValue = (encode input, state)
                result <- runInteractive replyTy remaining spent step
                  (toLift (SUProd (SUList SUNat) stateTy) inputValue)
                case result of
                  Left err -> pure (Left err)
                  Right (reply, remaining', spent')
                    | not (equalU replyTy (evalU sourceStep inputValue) reply) ->
                        pure (Left "surface/core evaluator disagreement")
                    | otherwise -> loop remaining' spent' reply
    finish spent = do
      when report (hPutStrLn stderr ("core work: " <> show spent))
      pure (Right ())

runCore :: SUTy b -> Morph a (Lift b) -> Val a -> Either String (UVal b, Natural)
runCore resultTy morph input =
  let value = evalV morph input
      (spent, gradedValue) = evalG workAlg morph input
  in case evalK morph input spent of
       Just (executed, 0)
         | equalLift resultTy value gradedValue
             && equalLift resultTy value executed ->
             Right (fromLift resultTy value, spent)
       _ -> Left "core evaluator disagreement"

runInteractive
  :: SUTy b
  -> Maybe Natural
  -> Natural
  -> Morph a (Lift b)
  -> Val a
  -> IO (Either String (UVal b, Maybe Natural, Natural))
runInteractive resultTy limit already morph input = pure $ do
  let value = evalV morph input
      (needed, gradedValue) = evalG workAlg morph input
      available = fromMaybe needed limit
  if available < needed
    then Left "core fuel exhausted"
    else case evalK morph input available of
      Just (executed, remaining)
        | equalLift resultTy value gradedValue
            && equalLift resultTy value executed ->
            Right (fromLift resultTy value, fmap (const remaining) limit, already + needed)
      _ -> Left "core evaluator disagreement"

equalU :: SUTy a -> UVal a -> UVal a -> Bool
equalU SUUnit _ _ = True
equalU SUNat a b = a == b
equalU (SUProd a b) (x, y) (x', y') = equalU a x x' && equalU b y y'
equalU (SUSum a _) (Left x) (Left y) = equalU a x y
equalU (SUSum _ b) (Right x) (Right y) = equalU b x y
equalU (SUSum _ _) _ _ = False
equalU (SUList a) xs ys = length xs == length ys && and (zipWith (equalU a) xs ys)

equalLift :: SUTy a -> Val (Lift a) -> Val (Lift a) -> Bool
equalLift SUUnit _ _ = True
equalLift SUNat a b = a == b
equalLift (SUProd a b) (x, y) (x', y') =
  equalLift a x x' && equalLift b y y'
equalLift (SUSum a _) (Left x) (Left y) = equalLift a x y
equalLift (SUSum _ b) (Right x) (Right y) = equalLift b x y
equalLift (SUSum _ _) _ _ = False
equalLift (SUList a) xs ys =
  length xs == length ys && and (zipWith (equalLift a) xs ys)

toLift :: SUTy a -> UVal a -> Val (Lift a)
toLift SUUnit x = x
toLift SUNat x = x
toLift (SUProd a b) (x, y) = (toLift a x, toLift b y)
toLift (SUSum a _) (Left x) = Left (toLift a x)
toLift (SUSum _ b) (Right x) = Right (toLift b x)
toLift (SUList a) xs = fmap (toLift a) xs

fromLift :: SUTy a -> Val (Lift a) -> UVal a
fromLift SUUnit x = x
fromLift SUNat x = x
fromLift (SUProd a b) (x, y) = (fromLift a x, fromLift b y)
fromLift (SUSum a _) (Left x) = Left (fromLift a x)
fromLift (SUSum _ b) (Right x) = Right (fromLift b x)
fromLift (SUList a) xs = fmap (fromLift a) xs

encode :: String -> [Natural]
encode = fmap (fromIntegral . ord)

decode :: [Natural] -> Either String String
decode = traverse decodeChar
  where
    decodeChar n
      | n > 0x10ffff = Left ("invalid Unicode scalar value " <> show n)
      | n >= 0xd800 && n <= 0xdfff = Left ("invalid Unicode surrogate " <> show n)
      | otherwise = Right (chr (fromIntegral n))
