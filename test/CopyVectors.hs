{-# LANGUAGE DataKinds #-}

module CopyVectors (copyVectors) where

import Telomare.Copyable
import Telomare.Core
import Telomare.Denotation

copyVectors :: [(String, Bool)]
copyVectors =
  [ ("copy-unit-value", evalV (copyS CopyUnit) () == ((), ()))
  , ("copy-nat-value", evalV (copyS CopyNat) 7 == (7, 7))
  , ("copy-nat-grade", dupGrade (copyS CopyNat) 7 == 1)
  , ("copy-product-value",
      evalV (copyS (CopyProd CopyNat CopyNat)) (3, 5)
        == ((3, 5), (3, 5)))
  , ("copy-product-grade",
      dupGrade (copyS (CopyProd CopyNat CopyNat)) (3, 5) == 2)
  , ("copy-bang-value",
      evalV (copyS (CopyBang (SList SNat))) [1, 2] == ([1, 2], [1, 2]))
  , ("copy-bang-grade",
      dupGrade (copyS (CopyBang (SList SNat))) [1, 2] == 5)
  ]
