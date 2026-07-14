{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Direct elaboration of the bang-free affine surface fragment.
--
-- This first compiler slice accepts every structural/data constructor,
-- guards, and the natural atom duplication exemption.  General contraction
-- and recursion require modal placement and are rejected explicitly.
module Telomare.Compiler.Direct
  ( DirectError (..)
  , RecursionKind (..)
  , Strip
  , compileDirect
  , eraseMorph
  , erasureMatches
  ) where

import Telomare.Core
import Telomare.Surface

data RecursionKind = Iteration | Fold | While
  deriving (Eq, Show)

data DirectError
  = GeneralDuplication
  | RecursionRequiresPlacement RecursionKind
  deriving (Eq, Show)

-- | Type-level erasure of core boxes.
type family Strip (a :: Ty) :: UTy where
  Strip 'Unit      = 'UUnit
  Strip 'Nat       = 'UNat
  Strip (a ':*: b) = Strip a ':**: Strip b
  Strip (a ':+: b) = Strip a ':++: Strip b
  Strip ('ListT a) = 'UList (Strip a)
  Strip ('Bang a)  = Strip a

stripSTy :: STy a -> SUTy (Strip a)
stripSTy SUnit       = SUUnit
stripSTy SNat        = SUNat
stripSTy (SProd a b) = SUProd (stripSTy a) (stripSTy b)
stripSTy (SSum a b)  = SUSum (stripSTy a) (stripSTy b)
stripSTy (SList a)   = SUList (stripSTy a)
stripSTy (SBang a)   = stripSTy a

-- | Compile the directly affine fragment into canonically lifted core types.
compileDirect :: UMorph a b -> Either DirectError (Morph (Lift a) (Lift b))
compileDirect UId            = Right IdS
compileDirect (g :..: f)     = (:.:) <$> compileDirect g <*> compileDirect f
compileDirect (f :****: g)   = (:***:) <$> compileDirect f <*> compileDirect g
compileDirect (UDup SUNat)   = Right DupNatS
compileDirect (UDup _)       = Left GeneralDuplication
compileDirect USwap          = Right SwapS
compileDirect UAssoc         = Right AssocS
compileDirect UUnassoc       = Right UnassocS
compileDirect UExl           = Right ExlS
compileDirect UExr           = Right ExrS
compileDirect UWeak          = Right WeakS
compileDirect URunit         = Right RunitS
compileDirect ULunit         = Right LunitS
compileDirect UInl           = Right InlS
compileDirect UInr           = Right InrS
compileDirect (UCase l r)    = CaseS <$> compileDirect l <*> compileDirect r
compileDirect UDistl         = Right DistlS
compileDirect UNil           = Right NilS
compileDirect UCons          = Right ConsS
compileDirect UUncons        = Right UnconsS
compileDirect UNatOut        = Right NatOutS
compileDirect USuc           = Right SucS
compileDirect UAdd           = Right AddS
compileDirect (UConst k)     = Right (ConstS k)
compileDirect (UGuard sa t)  = GuardS (liftSTy sa) <$> compileDirect t
compileDirect (UIter _)      = Left (RecursionRequiresPlacement Iteration)
compileDirect (UFold _)      = Left (RecursionRequiresPlacement Fold)
compileDirect (UWhile _ _ _) = Left (RecursionRequiresPlacement While)

-- | Erase every core exponential back to the cartesian surface syntax.
eraseMorph :: Morph a b -> UMorph (Strip a) (Strip b)
eraseMorph IdS            = UId
eraseMorph (g :.: f)      = eraseMorph g :..: eraseMorph f
eraseMorph (f :***: g)    = eraseMorph f :****: eraseMorph g
eraseMorph SwapS          = USwap
eraseMorph AssocS         = UAssoc
eraseMorph UnassocS       = UUnassoc
eraseMorph ExlS           = UExl
eraseMorph ExrS           = UExr
eraseMorph WeakS          = UWeak
eraseMorph RunitS         = URunit
eraseMorph LunitS         = ULunit
eraseMorph InlS           = UInl
eraseMorph InrS           = UInr
eraseMorph (CaseS l r)    = UCase (eraseMorph l) (eraseMorph r)
eraseMorph DistlS         = UDistl
eraseMorph NilS           = UNil
eraseMorph ConsS          = UCons
eraseMorph UnconsS        = UUncons
eraseMorph NatOutS        = UNatOut
eraseMorph SucS           = USuc
eraseMorph AddS           = UAdd
eraseMorph (ConstS k)     = UConst k
eraseMorph DupNatS        = UDup SUNat
eraseMorph (GuardS sa t)  = UGuard (stripSTy sa) (eraseMorph t)
eraseMorph (DupS sa)      = UDup (stripSTy sa)
eraseMorph (BoxS f)       = eraseMorph f
eraseMorph (BoxValS f)    = eraseMorph f
eraseMorph MergeS         = UId
eraseMorph (IterS f)      = UIter (eraseMorph f)
eraseMorph (FoldS f)      = UFold (eraseMorph f)
eraseMorph (WhileS sa t s) =
  UWhile (stripSTy sa) (eraseMorph t) (eraseMorph s)

-- | Independent structural check of the direct compiler's erasure law.
erasureMatches :: UMorph a b -> Either DirectError Bool
erasureMatches f = do
  core <- compileDirect f
  pure (shapeU (eraseMorph core) == shapeU f)
