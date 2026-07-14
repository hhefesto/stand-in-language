{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

-- | An intensional finite-grid-game frontend for typed core Morph programs.
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

import Control.Monad (foldM, unless, when)
import Data.Char (chr, ord)
import Data.List (intercalate, isPrefixOf)
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

data Player = Player String String

data Game = Game
  { gameRows         :: Int
  , gameColumns      :: Int
  , gameCells        :: Int
  , gamePlayers      :: [Player]
  , gameMoves        :: [String]
  , gameQuitInput    :: String
  , gameQuitMessage  :: String
  , gameWinningLines :: [[Int]]
  , gameCellSep      :: String
  , gameRowSep       :: String
  , gameTurnMessage  :: String
  , gamePrompt       :: String
  , gameInvalid      :: String
  , gameOccupied     :: String
  , gameWinMessage   :: String
  , gameTieMessage   :: String
  }

data Draft = Draft
  { draftBoard    :: Maybe (Int, Int)
  , draftCells    :: Maybe Int
  , draftPlayers  :: [Player]
  , draftMoves    :: Maybe [String]
  , draftQuit     :: Maybe (String, String)
  , draftLines    :: [[Int]]
  , draftCellSep  :: Maybe String
  , draftRowSep   :: Maybe String
  , draftTurn     :: Maybe String
  , draftPrompt   :: Maybe String
  , draftInvalid  :: Maybe String
  , draftOccupied :: Maybe String
  , draftWin      :: Maybe String
  , draftTie      :: Maybe String
  }

data Target = Goto String | Stay String | Stop String
data Rule = Rule String Target
data StateDecl = StateDecl String String [Rule] Target
type Board = [Maybe Int]

-- | Parse a finite-grid-game algebra and interpret it into two closed Morphs.
-- Finite reachable-state expansion is a compiler implementation detail, not
-- part of the source language or runtime representation.
compileMachine :: String -> Either MachineError Machine
compileMachine source = do
  game <- parseSource source
  let positions = reachable game
      states = fmap (positionState game) positions
      table = Map.fromList [(key, state) | state@(StateDecl key _ _ _) <- states]
  compiled <- traverse (compileState table (quitRule game)) states
  initial <- case states of
    state : _ -> Right state
    []        -> bad "game has no initial position"
  let initCore = constReply (stateDisplay initial) (Right (stateKey initial))
      missing = constReply "Internal machine state error.\n" (Left ())
      stepCore = foldr dispatchState missing compiled
  pure Machine
    { machineInit = initCore
    , machineStep = stepCore
    , machineStateCount = length states
    , machineRuleCount = sum [length rules + 2 | StateDecl _ _ rules _ <- states]
    }

stateKey :: StateDecl -> String
stateKey (StateDecl key _ _ _) = key

stateDisplay :: StateDecl -> String
stateDisplay (StateDecl _ display _ _) = display

quitRule :: Game -> Rule
quitRule game = Rule (gameQuitInput game) (Stop (gameQuitMessage game))

compileState
  :: Map.Map String StateDecl
  -> Rule
  -> StateDecl
  -> Either MachineError (String, Morph InputT ReplyT)
compileState table global (StateDecl key display rules fallback) = do
  branches <- traverse (compileRule table key display) (global : rules)
  fallbackCore <- compileTarget table key display fallback
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
  state <- maybe (bad ("unknown generated state " <> show target)) Right
    (Map.lookup target table)
  pure (constReply (stateDisplay state) (Right target))
compileTarget _ key display (Stay prefix) =
  pure (constReply (prefix <> display) (Right key))
compileTarget _ _ _ (Stop output) = pure (constReply output (Left ()))

positionState :: Game -> (Board, Int) -> StateDecl
positionState game (board, player) =
  StateDecl key display rules (Stay (gameInvalid game))
  where
    key = positionKey board player
    display = renderBoard game board <> renderTemplate game player (gameTurnMessage game)
      <> gamePrompt game
    rules = zipWith moveRule [0 ..] (gameMoves game)
    moveRule cell input
      | Just _ <- board !! cell = Rule input (Stay (gameOccupied game))
      | wins game board' player = Rule input
          (Stop (renderBoard game board' <> renderTemplate game player (gameWinMessage game)))
      | all occupied board' = Rule input (Stop (renderBoard game board' <> gameTieMessage game))
      | otherwise = Rule input (Goto (positionKey board' (nextPlayer game player)))
      where
        board' = replace cell (Just player) board

reachable :: Game -> [(Board, Int)]
reachable game = go [(replicate (gameCells game) Nothing, 0)] Map.empty
  where
    go [] _ = []
    go (position@(board, player) : queue) seen
      | Map.member key seen = go queue seen
      | otherwise = position : go (queue <> children) (Map.insert key () seen)
      where
        key = positionKey board player
        children =
          [ (board', nextPlayer game player)
          | cell <- [0 .. gameCells game - 1]
          , not (occupied (board !! cell))
          , let board' = replace cell (Just player) board
          , not (wins game board' player)
          , not (all occupied board')
          ]

positionKey :: Board -> Int -> String
positionKey board player = show player <> ":" <> intercalate "," (fmap cell board)
  where
    cell Nothing  = "_"
    cell (Just n) = show n

replace :: Int -> a -> [a] -> [a]
replace n value values = take n values <> [value] <> drop (n + 1) values

occupied :: Maybe a -> Bool
occupied Nothing  = False
occupied (Just _) = True

nextPlayer :: Game -> Int -> Int
nextPlayer game player = (player + 1) `mod` length (gamePlayers game)

wins :: Game -> Board -> Int -> Bool
wins game board player = any (all ((== Just player) . (board !!)))
  (gameWinningLines game)

renderBoard :: Game -> Board -> String
renderBoard game board = intercalate (gameRowSep game)
  [ intercalate (gameCellSep game) (fmap renderCell row)
  | row <- chunks (gameColumns game) (zip [0 :: Int ..] board)
  ] <> "\n"
  where
    renderCell (cell, Nothing)  = gameMoves game !! cell
    renderCell (_, Just player) = playerMark (gamePlayers game !! player)

chunks :: Int -> [a] -> [[a]]
chunks _ []     = []
chunks n values = take n values : chunks n (drop n values)

playerMark :: Player -> String
playerMark (Player _ mark) = mark

renderTemplate :: Game -> Int -> String -> String
renderTemplate game player = replaceAll "{mark}" mark . replaceAll "{player}" name
  where Player name mark = gamePlayers game !! player

replaceAll :: String -> String -> String -> String
replaceAll needle replacement = go
  where
    go [] = []
    go value@(char : rest)
      | needle `isPrefixOf` value = replacement <> go (drop (length needle) value)
      | otherwise = char : go rest

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

distRight :: Morph ((a ':+: b) ':*: c) ((a ':*: c) ':+: (b ':*: c))
distRight = CaseS (InlS :.: SwapS) (InrS :.: SwapS) :.: DistlS :.: SwapS

-- Failed comparisons reconstruct their input, so dispatch remains affine.
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
    rebuild :: Morph (('Nat ':*: TextT) ':+: ('Nat ':*: TextT)) (TextT ':+: TextT)
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
  where cons c rest = ConsS :.: (ConstS c :***: rest) :.: LunitS

encode :: String -> [Natural]
encode = fmap (fromIntegral . ord)

decode :: [Natural] -> String
decode = fmap (chr . fromIntegral)

-- | Every scripted transition is checked through all three core semantics.
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

runMachineIO :: Maybe Natural -> Bool -> Machine -> IO (Either String ())
runMachineIO fuel report machine = do
  result <- runInteractive fuel 0 (machineInit machine) ()
  case result of
    Left err                        -> pure (Left err)
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
              Left err                          -> pure (Left err)
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

parseSource :: String -> Either MachineError Game
parseSource source = case filter significant (zip [1 :: Int ..] (lines source)) of
  ((_, "telomare-grid-game 1") : rest) -> validate =<< foldM parseLine emptyDraft rest
  ((line, _) : _) -> badAt line "expected telomare-grid-game 1 header"
  [] -> bad "empty source"
  where
    significant (_, line) = not (all (== ' ') line)
      && not ("#" `isPrefixOf` dropWhile (== ' ') line)

emptyDraft :: Draft
emptyDraft = Draft Nothing Nothing [] Nothing Nothing [] Nothing Nothing Nothing
  Nothing Nothing Nothing Nothing Nothing

parseLine :: Draft -> (Int, String) -> Either MachineError Draft
parseLine draft (lineNo, input)
  | Just rest <- stripWord "board" input = do
      values <- integers lineNo rest
      case values of
        [rows, columns] -> setOnce lineNo "board" (draftBoard draft)
          (\value -> draft {draftBoard = Just value}) (rows, columns)
        _ -> badAt lineNo "board expects ROWS COLUMNS"
  | Just rest <- stripWord "cells" input = do
      value <- integer lineNo rest
      setOnce lineNo "cells" (draftCells draft)
        (\n -> draft {draftCells = Just n}) value
  | Just rest <- stripWord "player" input = do
      (name, mark) <- twoQuoted lineNo rest
      pure draft {draftPlayers = draftPlayers draft <> [Player name mark]}
  | Just rest <- stripWord "moves" input = do
      values <- quotedList lineNo rest
      setOnce lineNo "moves" (draftMoves draft)
        (\moves -> draft {draftMoves = Just moves}) values
  | Just rest <- stripWord "quit" input = do
      value <- twoQuoted lineNo rest
      setOnce lineNo "quit" (draftQuit draft)
        (\quit -> draft {draftQuit = Just quit}) value
  | Just rest <- stripWord "winning" input = do
      values <- integers lineNo rest
      pure draft {draftLines = draftLines draft <> [fmap (subtract 1) values]}
  | otherwise = parseTextDeclaration draft lineNo input

parseTextDeclaration :: Draft -> Int -> String -> Either MachineError Draft
parseTextDeclaration draft lineNo input
  | Just rest <- stripWord "cell-separator" input = text "cell-separator" draftCellSep
      (\v -> draft {draftCellSep = Just v}) rest
  | Just rest <- stripWord "row-separator" input = text "row-separator" draftRowSep
      (\v -> draft {draftRowSep = Just v}) rest
  | Just rest <- stripWord "turn-message" input = text "turn-message" draftTurn
      (\v -> draft {draftTurn = Just v}) rest
  | Just rest <- stripWord "prompt" input = text "prompt" draftPrompt
      (\v -> draft {draftPrompt = Just v}) rest
  | Just rest <- stripWord "invalid-message" input = text "invalid-message" draftInvalid
      (\v -> draft {draftInvalid = Just v}) rest
  | Just rest <- stripWord "occupied-message" input = text "occupied-message" draftOccupied
      (\v -> draft {draftOccupied = Just v}) rest
  | Just rest <- stripWord "win-message" input = text "win-message" draftWin
      (\v -> draft {draftWin = Just v}) rest
  | Just rest <- stripWord "tie-message" input = text "tie-message" draftTie
      (\v -> draft {draftTie = Just v}) rest
  | otherwise = badAt lineNo "unrecognised declaration"
  where
    text name field setter rest = do
      value <- quoted lineNo rest
      setOnce lineNo name (field draft) setter value

setOnce :: Int -> String -> Maybe a -> (a -> Draft) -> a -> Either MachineError Draft
setOnce line name old setter value = case old of
  Just _  -> badAt line ("duplicate " <> name <> " declaration")
  Nothing -> Right (setter value)

validate :: Draft -> Either MachineError Game
validate draft = do
  (rows, columns) <- required "board" (draftBoard draft)
  cells <- required "cells" (draftCells draft)
  moves <- required "moves" (draftMoves draft)
  (quitInput, quitMessage) <- required "quit" (draftQuit draft)
  cellSep <- required "cell-separator" (draftCellSep draft)
  rowSep <- required "row-separator" (draftRowSep draft)
  turn <- required "turn-message" (draftTurn draft)
  prompt <- required "prompt" (draftPrompt draft)
  invalid <- required "invalid-message" (draftInvalid draft)
  occupiedMessage <- required "occupied-message" (draftOccupied draft)
  win <- required "win-message" (draftWin draft)
  tie <- required "tie-message" (draftTie draft)
  let players = draftPlayers draft
      winningLines = draftLines draft
      unique values = length values == Map.size (Map.fromList [(value, ()) | value <- values])
      playerNames = [name | Player name _ <- players]
      marks = [mark | Player _ mark <- players]
  unless (rows > 0 && columns > 0 && cells == rows * columns)
    (bad "board dimensions must be positive and multiply to cells")
  unless (length players >= 2) (bad "at least two players are required")
  unless (not (any null playerNames) && not (any null marks) && unique marks)
    (bad "player names and distinct marks must be non-empty")
  unless (length moves == cells && not (any null moves) && unique moves)
    (bad "moves must contain one distinct non-empty input per cell")
  unless (not (null quitInput) && quitInput `notElem` moves)
    (bad "quit input must be non-empty and distinct from moves")
  unless (not (null winningLines) && all (validLine cells) winningLines)
    (bad "winning lines must be non-empty, distinct in-range cell indices")
  pure Game
    { gameRows = rows, gameColumns = columns, gameCells = cells
    , gamePlayers = players, gameMoves = moves
    , gameQuitInput = quitInput, gameQuitMessage = quitMessage
    , gameWinningLines = winningLines, gameCellSep = cellSep, gameRowSep = rowSep
    , gameTurnMessage = turn, gamePrompt = prompt, gameInvalid = invalid
    , gameOccupied = occupiedMessage, gameWinMessage = win, gameTieMessage = tie
    }
validLine :: Int -> [Int] -> Bool
validLine cells values = not (null values) && all (\n -> n >= 0 && n < cells) values
  && length values == Map.size (Map.fromList [(value, ()) | value <- values])

required :: String -> Maybe a -> Either MachineError a
required name = maybe (bad ("missing " <> name <> " declaration")) Right

integer :: Int -> String -> Either MachineError Int
integer line input = case reads input of
  [(value, rest)] | all (== ' ') rest -> Right value
  _                                   -> badAt line "expected integer"

integers :: Int -> String -> Either MachineError [Int]
integers line input = traverse readOne (words input)
  where
    readOne value = case reads value of
      [(n, "")] -> Right n
      _         -> badAt line "expected integers"

quoted :: Int -> String -> Either MachineError String
quoted line input = do
  (value, rest) <- firstQuoted line input
  if all (== ' ') rest then Right value else badAt line "trailing input"

twoQuoted :: Int -> String -> Either MachineError (String, String)
twoQuoted line input = do
  (first, rest) <- firstQuoted line input
  second <- quoted line rest
  pure (first, second)

quotedList :: Int -> String -> Either MachineError [String]
quotedList line = go [] . dropWhile (== ' ')
  where
    go values [] = Right (reverse values)
    go values input = do
      (value, rest) <- firstQuoted line input
      go (value : values) rest

firstQuoted :: Int -> String -> Either MachineError (String, String)
firstQuoted line input = case reads input of
  [(value, rest)] -> Right (value, dropWhile (== ' ') rest)
  _               -> badAt line "expected quoted string"

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
