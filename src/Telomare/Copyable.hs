{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | Costed core copying, mirroring @T3.Core.Copyable@.  The 'Copyable'
-- evidence lives in "Telomare.Core" (total on first-order data; future
-- non-data objects will have no witness) and 'copyS' is the primitive
-- 'CopyS' — a structural list copy is not derivable at level 0, which is
-- why the primitive exists.  The dup grade charges its full 'sizeVal'.
-- The surface-to-core witness 'copyableLift' lives in
-- "Telomare.Compiler.Direct" beside the 'Lift' family it produces.
module Telomare.Copyable
  ( Copyable (..)
  , copyS
  ) where

import Telomare.Core

copyS :: Copyable a -> Morph a (a ':*: a)
copyS = CopyS
