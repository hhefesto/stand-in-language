{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | Explicitly witnessed core copying, mirroring @T3.Core.Copyable@.
-- There is deliberately no catch-all witness: copying remains an operation
-- supplied by the type's algebra, not ambient variable reuse.
module Telomare.Copyable
  ( Copyable (..)
  , copyS
  ) where

import Telomare.Core

data Copyable a where
  CopyUnit :: Copyable 'Unit
  CopyNat  :: Copyable 'Nat
  CopyProd :: Copyable a -> Copyable b -> Copyable (a ':*: b)
  CopyBang :: STy a -> Copyable ('Bang a)

copyS :: Copyable a -> Morph a (a ':*: a)
copyS CopyUnit       = LunitS
copyS CopyNat        = DupNatS
copyS (CopyProd a b) = shuffle :.: (copyS a :***: copyS b)
copyS (CopyBang a)   = DupS a

shuffle :: Morph ((a ':*: a) ':*: (b ':*: b))
                 ((a ':*: b) ':*: (a ':*: b))
shuffle = AssocS
  :.: (UnassocS :***: IdS)
  :.: ((IdS :***: SwapS) :***: IdS)
  :.: UnassocS
  :.: (IdS :***: UnassocS)
  :.: AssocS
