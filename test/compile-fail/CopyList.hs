{-# LANGUAGE LinearTypes #-}

module CopyList where

import Numeric.Natural (Natural)

import Telomare.Linear

bad :: Circuit [Natural] ([Natural], [Natural])
bad = copy CopyNatural
