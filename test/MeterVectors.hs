module MeterVectors (meterVectors) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.List (findIndex, isInfixOf, isPrefixOf)
import qualified Data.Map as Map

import Telomare.Compat.Parser (parseModuleNamed)
import Telomare.Compat.Syntax (AnnotatedUPT (..), HighTermF (RecursionF),
                               LocTag (..), SourcePosition (..),
                               SourceSpan (..), UnprocessedParsedTermF (..),
                               UnsizedRecursionToken (..))
import Telomare.Tel.Eval (Meter (..), RecursionSite (..), combineMeters,
                          renderMeter)

meterVectors :: [(String, Bool)]
meterVectors =
  [ ("meter sums unrolls per source site", sumsUnrolls)
  , ("meter renders readable source-aware table", rendersTable)
  , ("meter orders hottest recursion sites first", ordersHotSites)
  , ("parser keeps module filename in recursion source span", keepsFilename)
  ]

site0 :: RecursionSite
site0 = RecursionSite (UnsizedRecursionToken 0) (sourceLoc "game.tel" 12 3) (Just "game.foldr")

site1 :: RecursionSite
site1 = RecursionSite (UnsizedRecursionToken 1) (sourceLoc "game.tel" 20 7) (Just "game.map")

sourceLoc :: FilePath -> Int -> Int -> LocTag
sourceLoc file line col = SourceLoc SourceSpan
  { sourceSpanFile = Just file
  , sourceSpanStart = SourcePosition line col 0
  , sourceSpanEnd = SourcePosition line col 0
  }

combined :: Meter
combined = combineMeters
  (Meter 999 5 (Map.fromList [(site0, 1)]))
  (Meter 1000 6 (Map.fromList [(site0, 2), (site1, 20)]))

sumsUnrolls :: Bool
sumsUnrolls =
  mApplies combined == 1999
  && mGates combined == 11
  && Map.lookup site0 (mUnrolls combined) == Just 3
  && Map.lookup site1 (mUnrolls combined) == Just 20

report :: String
report = renderMeter combined

rendersTable :: Bool
rendersTable = all (`isInfixOf` report)
  [ "function applications: 1,999"
  , "gate selections:        11"
  , "recursion unrolls:      23 across 2 sites"
  , "site"
  , "source"
  , "function"
  , "#0"
  , "#1"
  , "game.tel:12:3"
  , "game.tel:20:7"
  , "game.foldr"
  , "game.map"
  ]

ordersHotSites :: Bool
ordersHotSites = case (lineIndex "  #1", lineIndex "  #0") of
  (Just hot, Just cool) -> hot < cool
  _                     -> False
  where
    lineIndex prefix = findIndex (isPrefixOf prefix) (lines report)

keepsFilename :: Bool
keepsFilename = case parseModuleNamed "demo.tel" "main = {0, 0, 0}\n" of
  Right [Right ("main", AnnotatedUPT (SourceLoc span' :< UnprocessedParsedTermH (RecursionF _ _ _)))] ->
    sourceSpanFile span' == Just "demo.tel"
  _ -> False
