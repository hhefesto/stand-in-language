{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Direct elaboration of the bang-free affine surface fragment.
--
-- This first compiler slice accepts every structural/data constructor,
-- guards, and costed duplication at every copyable (first-order data)
-- type — 'UDup' compiles to the priced 'CopyS', with 'DupNatS' retained
-- as the historical atom exemption at 'SUNat'.  Recursion requires modal
-- placement and is rejected explicitly.  'GeneralDuplication' is
-- currently unreachable; it returns when non-copyable objects (arrows)
-- enter the surface.
module Telomare.Compiler.Direct
  ( DirectError (..)
  , RecursionKind (..)
  , Strip
  , compileDirect
  , copyableLift
  , stripCopyable
  , stripSTy
  , eraseMorph
  , erasureMatches
  ) where

import Telomare.Core
import Telomare.Surface

data RecursionKind = Mapping | Iteration | Fold | While | MappingClosure
  deriving (Eq, Show)

data DirectError
  = GeneralDuplication
  | RecursionRequiresPlacement RecursionKind
  deriving (Eq, Show)

-- | Type-level erasure of core boxes.
type family Strip (a :: Ty) :: UTy where
  Strip 'Unit        = 'UUnit
  Strip 'Nat         = 'UNat
  Strip (a ':*: b)   = Strip a ':**: Strip b
  Strip (a ':+: b)   = Strip a ':++: Strip b
  Strip ('ListT a)   = 'UList (Strip a)
  Strip ('Bang a)    = Strip a
  Strip ('Lolly a b) = 'ULolly (Strip a) (Strip b)

stripSTy :: STy a -> SUTy (Strip a)
stripSTy SUnit        = SUUnit
stripSTy SNat         = SUNat
stripSTy (SProd a b)  = SUProd (stripSTy a) (stripSTy b)
stripSTy (SSum a b)   = SUSum (stripSTy a) (stripSTy b)
stripSTy (SList a)    = SUList (stripSTy a)
stripSTy (SBang a)    = stripSTy a
stripSTy (SLolly a b) = SULolly (stripSTy a) (stripSTy b)

-- | Every first-order surface type lifts to a copyable core type.
-- 'Maybe' so a future non-copyable surface object (arrows) is a clean
-- 'Nothing' rather than a partial match.
copyableLift :: SUTy a -> Maybe (Copyable (Lift a))
copyableLift SUUnit        = Just CopyUnit
copyableLift SUNat         = Just CopyNat
copyableLift (SUProd a b)  = CopyProd <$> copyableLift a <*> copyableLift b
copyableLift (SUSum a b)   = CopySum <$> copyableLift a <*> copyableLift b
copyableLift (SUList a)    = CopyList <$> copyableLift a
copyableLift (SULolly _ _) = Nothing
  -- a closure is code; its duplication goes through Bang, never CopyS

-- | The surface singleton a copy witness erases to.
stripCopyable :: Copyable a -> SUTy (Strip a)
stripCopyable CopyUnit       = SUUnit
stripCopyable CopyNat        = SUNat
stripCopyable (CopyProd a b) = SUProd (stripCopyable a) (stripCopyable b)
stripCopyable (CopySum a b)  = SUSum (stripCopyable a) (stripCopyable b)
stripCopyable (CopyList a)   = SUList (stripCopyable a)
stripCopyable (CopyBang s)   = stripSTy s

-- | Compile the directly affine fragment into canonically lifted core types.
compileDirect :: UMorph a b -> Either DirectError (Morph (Lift a) (Lift b))
compileDirect UId            = Right IdS
compileDirect (g :..: f)     = (:.:) <$> compileDirect g <*> compileDirect f
compileDirect (f :****: g)   = (:***:) <$> compileDirect f <*> compileDirect g
compileDirect (UDup SUNat)   = Right DupNatS
compileDirect (UDup sa)      =
  maybe (Left GeneralDuplication) (Right . CopyS) (copyableLift sa)
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
compileDirect (UCurry sc f)  = CurryS (liftSTy sc) <$> compileDirect f
compileDirect UApply         = Right ApplyS
compileDirect UMapC          = Left (RecursionRequiresPlacement MappingClosure)
compileDirect (UGuard sa t)  = GuardS (liftSTy sa) <$> compileDirect t
compileDirect (UMap _)       = Left (RecursionRequiresPlacement Mapping)
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
eraseMorph (CopyS w)      = UDup (stripCopyable w)
eraseMorph (CurryS sc f)  = UCurry (stripSTy sc) (eraseMorph f)
eraseMorph ApplyS         = UApply
eraseMorph MapCS          = UMapC
eraseMorph (GuardS sa t)  = UGuard (stripSTy sa) (eraseMorph t)
eraseMorph (DupS sa)      = UDup (stripSTy sa)
eraseMorph (BoxS f)       = eraseMorph f
eraseMorph (BoxValS f)    = eraseMorph f
eraseMorph MergeS         = UId
eraseMorph (MapS f)       = UMap (eraseMorph f)
eraseMorph (IterS f)      = UIter (eraseMorph f)
eraseMorph (FoldS f)      = UFold (eraseMorph f)
eraseMorph (WhileS sa t s) =
  UWhile (stripSTy sa) (eraseMorph t) (eraseMorph s)

-- | Independent structural check of the direct compiler's erasure law.
erasureMatches :: UMorph a b -> Either DirectError Bool
erasureMatches f = do
  core <- compileDirect f
  pure (shapeU (eraseMorph core) == shapeU f)
