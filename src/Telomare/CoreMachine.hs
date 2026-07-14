{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

-- | A deliberately small .tel2 frontend for declarative finite machines.
-- Source declarations are resolved to two closed, typed core artifacts; the
-- driver never receives an executable Haskell transition function.
module Telomare.CoreMachine
  ( TextT
  , StateT
  , InputT
  , ReplyT
  , Machine (..)
  , MachineError (..)
  , compileMachine
  , runMachineScript
  , runMachineIO
  ) where

import Control.Monad (foldM, when)
import Data.Char (chr, ord)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Numeric.Natural (Natural)
import System.IO (hFlush, hPutStrLn, isEOF, stderr, stdout)

import Telomare.Core
import Telomare.Denotation

type TextT = 'ListT 'Nat
type StateT = 'ListT 'Nat
type InputT = TextT ':*: StateT
type ReplyT = TextT ':*: ('Unit ':+: StateT)

data Machine = Machine
  { machineInit       :: Morph 'Unit ReplyT
  , machineStep       :: Morph InputT ReplyT
  , machineStateCount :: Int
  , machineRuleCount  :: Int
  }

newtype MachineError = MachineError String
  deriving (Eq, Show)

data Target = Goto String | Stay String | Stop String
data Rule = Rule String Target
data StateDecl = StateDecl String String [Rule] (Maybe Target)
data Source = Source (Maybe String) [Rule] [StateDecl]

-- | Parse and compile the finite-machine subset. Its grammar is line based:
-- @initial STATE@, @global INPUT stop TEXT@,
-- @state STATE DISPLAY@, @on INPUT (goto STATE|stay PREFIX|stop TEXT)@, and
-- @default (stay PREFIX|stop TEXT)@. All strings use Haskell escapes.
compileMachine :: String -> Either MachineError Machine
compileMachine source = do
  Source initial globals states <- parseSource source
  initialKey <- maybe (bad "missing initial declaration") Right initial
  table <- foldM insertState Map.empty states
  initialState <- lookupState table initialKey
  compiledStates <- traverse (compileState table globals) states
  let initCore = constReply (stateDisplay initialState) (Right initialKey)
      missing = constReply "Internal machine state error.\n" (Left ())
      stepCore = foldr dispatchState missing compiledStates
      rules = length globals + sum (fmap countRules states)
  pure Machine
    { machineInit = initCore
    , machineStep = stepCore
    , machineStateCount = length states
    , machineRuleCount = rules
    }
  where
    insertState table state@(StateDecl key _ _ _)
      | Map.member key table = bad ("duplicate state " <> show key)
      | otherwise = Right (Map.insert key state table)
    countRules (StateDecl _ _ rs d) = length rs + maybe 0 (const 1) d

stateDisplay :: StateDecl -> String
stateDisplay (StateDecl _ display _ _) = display

lookupState :: Map.Map String StateDecl -> String -> Either MachineError StateDecl
lookupState table key = maybe (bad ("unknown state " <> show key)) Right (Map.lookup key table)

compileState
  :: Map.Map String StateDecl
  -> [Rule]
  -> StateDecl
  -> Either MachineError (String, Morph InputT ReplyT)
compileState table globals (StateDecl key display rules fallback) = do
  branches <- traverse (compileRule table key display) (globals <> rules)
  fallbackCore <- maybe (bad ("state " <> show key <> " has no default rule"))
    (compileTarget table key display) fallback
  pure (key, foldr dispatchInput fallbackCore branches)

compileRule
  :: Map.Map String StateDecl
  -> String
  -> String
  -> Rule
  -> Either MachineError (String, Morph InputT ReplyT)
compileRule table key display (Rule input target) = do
  core <- compileTarget table key display target
  pure (input, core)

compileTarget
  :: Map.Map String StateDecl
  -> String
  -> String
  -> Target
  -> Either MachineError (Morph InputT ReplyT)
compileTarget table _ _ (Goto target) = do
  state <- lookupState table target
  pure (constReply (stateDisplay state) (Right target))
compileTarget _ key display (Stay prefix) =
  pure (constReply (prefix <> display) (Right key))
compileTarget _ _ _ (Stop output) = pure (constReply output (Left ()))

dispatchState
  :: (String, Morph InputT ReplyT)
  -> Morph InputT ReplyT
  -> Morph InputT ReplyT
dispatchState (key, hit) miss =
  CaseS hit miss :.: DistlS :.: (IdS :***: partitionText (encode key))

dispatchInput
  :: (String, Morph InputT ReplyT)
  -> Morph InputT ReplyT
  -> Morph InputT ReplyT
dispatchInput (input, hit) miss =
  CaseS hit miss :.: distRight :.: (partitionText (encode input) :***: IdS)

-- | Distribute a coproduct in the left component of a product.
distRight :: Morph ((a ':+: b) ':*: c) ((a ':*: c) ':+: (b ':*: c))
distRight = CaseS (InlS :.: SwapS) (InrS :.: SwapS) :.: DistlS :.: SwapS

-- These partitions are linear: every mismatch branch reconstructs exactly
-- the value it consumed. No ambient host equality or hidden copy is involved.
partitionNat :: Natural -> Morph 'Nat ('Nat ':+: 'Nat)
partitionNat 0 = CaseS (InlS :.: ConstS 0) (InrS :.: SucS) :.: NatOutS
partitionNat n = CaseS (InrS :.: ConstS 0) recur :.: NatOutS
  where
    recur = CaseS (InlS :.: SucS) (InrS :.: SucS) :.: partitionNat (n - 1)

partitionText :: [Natural] -> Morph TextT (TextT ':+: TextT)
partitionText [] = CaseS (InlS :.: NilS) (InrS :.: ConsS) :.: UnconsS
partitionText (c : cs) = CaseS empty nonempty :.: UnconsS
  where
    empty :: Morph 'Unit (TextT ':+: TextT)
    empty = InrS :.: NilS
    nonempty :: Morph ('Nat ':*: TextT) (TextT ':+: TextT)
    nonempty = rebuild :.: distRight :.: (partitionNat c :***: IdS)
    rebuild :: Morph (('Nat ':*: TextT) ':+: ('Nat ':*: TextT))
                     (TextT ':+: TextT)
    rebuild = CaseS matching (InrS :.: ConsS)
    matching :: Morph ('Nat ':*: TextT) (TextT ':+: TextT)
    matching = CaseS (InlS :.: ConsS) (InrS :.: ConsS)
      :.: DistlS :.: (IdS :***: partitionText cs)

constReply :: String -> Either () String -> Morph a ReplyT
constReply output continuation =
  (constText output :***: constContinuation continuation) :.: LunitS :.: WeakS

constContinuation :: Either () String -> Morph 'Unit ('Unit ':+: StateT)
constContinuation (Left ())  = InlS
constContinuation (Right st) = InrS :.: constText st

constText :: String -> Morph 'Unit TextT
constText = foldr cons NilS . encode
  where
    cons c rest = ConsS :.: (ConstS c :***: rest) :.: LunitS

encode :: String -> [Natural]
encode = fmap (fromIntegral . ord)

decode :: [Natural] -> String
decode = fmap (chr . fromIntegral)

-- | Scripted pure driver used by tests. Each transition is checked through
-- evalV, evalG/workAlg, and evalK with exactly the denoted work budget.
runMachineScript :: Machine -> [String] -> Either String (String, Natural)
runMachineScript machine inputs = do
  (reply, initialWork) <- runCore (machineInit machine) ()
  go (decode (fst reply)) initialWork (snd reply) inputs
  where
    go transcript total (Left ()) _ = Right (transcript, total)
    go transcript total (Right _) [] = Right (transcript, total)
    go transcript total (Right state) (input : rest) = do
      (reply, spent) <- runCore (machineStep machine) (encode input, state)
      go (transcript <> decode (fst reply)) (total + spent) (snd reply) rest

runCore :: Eq (Val b) => Morph a b -> Val a -> Either String (Val b, Natural)
runCore morph input =
  let value = evalV morph input
      (spent, gradedValue) = evalG workAlg morph input
  in case evalK morph input spent of
       Just (executed, 0)
         | value == gradedValue && value == executed -> Right (value, spent)
       _ -> Left "core evaluator disagreement"

-- | Host I/O driver. Parsing input and rendering Text are its only semantic
-- responsibilities; all state transitions and replies come from Morph.
runMachineIO :: Maybe Natural -> Bool -> Machine -> IO (Either String ())
runMachineIO fuel report machine = do
  result <- runInteractive fuel 0 (machineInit machine) ()
  case result of
    Left err -> pure (Left err)
    Right (reply, remaining, spent) -> loop remaining spent reply
  where
    loop remaining spent (output, continuation) = do
      putStr (decode output)
      hFlush stdout
      case continuation of
        Left () -> finish spent
        Right state -> do
          eof <- isEOF
          if eof then finish spent else do
            input <- getLine
            result <- runInteractive remaining spent (machineStep machine) (encode input, state)
            case result of
              Left err -> pure (Left err)
              Right (reply, remaining', spent') -> loop remaining' spent' reply
    finish spent = do
      when report (hPutStrLn stderr ("core work: " <> show spent))
      pure (Right ())

runInteractive
  :: Eq (Val b)
  => Maybe Natural
  -> Natural
  -> Morph a b
  -> Val a
  -> IO (Either String (Val b, Maybe Natural, Natural))
runInteractive limit already morph input = pure $ do
  let value = evalV morph input
      (needed, gradedValue) = evalG workAlg morph input
      available = fromMaybe needed limit
  if available < needed
    then Left "core fuel exhausted"
    else case evalK morph input available of
      Just (executed, remaining)
        | value == gradedValue && value == executed ->
            Right (value, fmap (const remaining) limit, already + needed)
      _ -> Left "core evaluator disagreement"

parseSource :: String -> Either MachineError Source
parseSource source = case filter significant (zip [1 :: Int ..] (lines source)) of
  ((_, "telomare-finite-machine 1") : rest) -> finish =<< foldM parseLine empty rest
  ((line, _) : _) -> badAt line "expected telomare-finite-machine 1 header"
  [] -> bad "empty source"
  where
    significant (_, line) = not (null line) && not ("#" `isPrefixOf` line)
    empty = (Nothing, [], [], Nothing)
    finish (initial, globals, states, current) =
      Right (Source initial globals (states <> foldMap pure current))

parseLine
  :: (Maybe String, [Rule], [StateDecl], Maybe StateDecl)
  -> (Int, String)
  -> Either MachineError (Maybe String, [Rule], [StateDecl], Maybe StateDecl)
parseLine (initial, globals, states, current) (lineNo, line)
  | Just rest <- stripWord "initial" line = do
      key <- quoted lineNo rest
      pure (Just key, globals, states, current)
  | Just rest <- stripWord "global" line = do
      (input, target) <- ruleParts lineNo rest
      pure (initial, globals <> [Rule input target], states, current)
  | Just rest <- stripWord "state" line = do
      (key, display) <- twoQuoted lineNo rest
      pure (initial, globals, states <> foldMap pure current,
            Just (StateDecl key display [] Nothing))
  | Just rest <- stripWord "on" line = do
      state <- maybe (badAt lineNo "on outside a state") Right current
      (input, target) <- ruleParts lineNo rest
      let StateDecl key display rules fallback = state
      pure (initial, globals, states,
            Just (StateDecl key display (rules <> [Rule input target]) fallback))
  | Just rest <- stripWord "default" line = do
      state <- maybe (badAt lineNo "default outside a state") Right current
      target <- targetParts lineNo rest
      let StateDecl key display rules _ = state
      pure (initial, globals, states, Just (StateDecl key display rules (Just target)))
  | otherwise = badAt lineNo "unrecognised declaration"

ruleParts :: Int -> String -> Either MachineError (String, Target)
ruleParts line input = do
  (label, rest) <- firstQuoted line input
  target <- targetParts line rest
  pure (label, target)

targetParts :: Int -> String -> Either MachineError Target
targetParts line input
  | Just rest <- stripWord "goto" input = Goto <$> quoted line rest
  | Just rest <- stripWord "stay" input = Stay <$> quoted line rest
  | Just rest <- stripWord "stop" input = Stop <$> quoted line rest
  | otherwise = badAt line "expected goto, stay, or stop"

quoted :: Int -> String -> Either MachineError String
quoted line input = do
  (value, rest) <- firstQuoted line input
  if all (== ' ') rest then Right value else badAt line "trailing input"

twoQuoted :: Int -> String -> Either MachineError (String, String)
twoQuoted line input = do
  (first, rest) <- firstQuoted line input
  second <- quoted line rest
  pure (first, second)

firstQuoted :: Int -> String -> Either MachineError (String, String)
firstQuoted line input = case reads input of
  [(value, rest)] -> Right (value, dropWhile (== ' ') rest)
  _ -> badAt line "expected quoted string"

stripWord :: String -> String -> Maybe String
stripWord word input = dropWhile (== ' ') <$> stripPrefix (word <> " ") input
  where
    stripPrefix prefix value
      | prefix `isPrefixOf` value = Just (drop (length prefix) value)
      | otherwise = Nothing

bad :: String -> Either MachineError a
bad = Left . MachineError

badAt :: Int -> String -> Either MachineError a
badAt line message = bad ("line " <> show line <> ": " <> message)
