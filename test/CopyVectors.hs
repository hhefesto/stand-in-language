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
  , ("copy-unit-grade", dupGrade (copyS CopyUnit) () == 1)
  , ("copy-sum-value",
      evalV (copyS (CopySum CopyUnit CopyNat)) (Right 4)
        == (Right 4, Right 4))
  , ("copy-sum-grade",
      dupGrade (copyS (CopySum CopyUnit CopyNat)) (Right 4) == 2)
  , ("copy-list-value",
      evalV (copyS (CopyList CopyNat)) [1, 2, 3] == ([1, 2, 3], [1, 2, 3]))
  , ("copy-list-grade", dupGrade (copyS (CopyList CopyNat)) [1, 2, 3] == 7)
  , ("copy-work-free", work (copyS (CopyList CopyNat)) [1, 2, 3] == 0)
  ]
