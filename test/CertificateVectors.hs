module CertificateVectors (certificateVectors) where

import Data.List (isInfixOf)

import Telomare.Compat.Levels (levelsReport)

certificateVectors :: [(String, Bool)]
certificateVectors =
  [ ("certificate explains compatibility scope", explainsScope)
  , ("certificate groups repeated source-site levels", groupsRepeatedSite)
  , ("certificate shows qualified owners and source files", showsOwnersAndFiles)
  , ("certificate avoids old misleading labels", avoidsOldLabels)
  , ("certificate separates report from program output", hasEndMarker)
  ]

report :: String
report = levelsReport [("Main", mainSource)] "Main"

mainSource :: String
mainSource = unlines
  [ "helper = {0, 0, 0}"
  , "wrap = \\p -> {0, p, 0}"
  , "main = (helper, wrap helper)"
  ]

explainsScope :: Bool
explainsScope = all (`isInfixOf` report)
  [ "-- Telomare structural placement certificate"
  , "analysis: static compatibility approximation; the program has not run"
  , "Use --meter for"
  , "How to read a level"
  , "Paths are static dependency witnesses, not runtime call traces"
  ]

groupsRepeatedSite :: Bool
groupsRepeatedSite = all (`isInfixOf` report)
  [ "Main.tel:1:11"
  , "Main.helper"
  , "0, 1"
  ]

showsOwnersAndFiles :: Bool
showsOwnersAndFiles = all (`isInfixOf` report)
  [ "entry: Main.main"
  , "Main.wrap"
  , "Main.tel:2:15"
  , "Binding depth pressure"
  , "Main.wrap.p"
  ]

avoidsOldLabels :: Bool
avoidsOldLabels = not ("towerHeight" `isInfixOf` report)
  && not ("forced under" `isInfixOf` report)
  && "maximum inferred recursion-box depth" `isInfixOf` report
  && "depth delta" `isInfixOf` report

hasEndMarker :: Bool
hasEndMarker = "-- End certificate; program output follows" `isInfixOf` report
