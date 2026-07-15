{-# LANGUAGE LinearTypes #-}

module Drop where

import Numeric.Natural (Natural)

import Telomare.Linear

bad :: Wire s Natural Natural %1 -> Wire s Natural Natural
bad _ = identity
