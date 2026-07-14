{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module SurfaceVectors (surfaceVectors) where

import Telomare.Compiler.Direct
import Telomare.Core (Val)
import Telomare.Denotation (evalV)
import Telomare.Surface

toCore :: SUTy a -> UVal a -> Val (Lift a)
toCore SUUnit       ()         = ()
toCore SUNat        n          = n
toCore (SUProd a b) (x, y)     = (toCore a x, toCore b y)
toCore (SUSum a _)  (Left x)   = Left (toCore a x)
toCore (SUSum _ b)  (Right y)  = Right (toCore b y)
toCore (SUList a)   xs         = fmap (toCore a) xs

fromCore :: SUTy a -> Val (Lift a) -> UVal a
fromCore SUUnit       ()         = ()
fromCore SUNat        n          = n
fromCore (SUProd a b) (x, y)     = (fromCore a x, fromCore b y)
fromCore (SUSum a _)  (Left x)   = Left (fromCore a x)
fromCore (SUSum _ b)  (Right y)  = Right (fromCore b y)
fromCore (SUList a)   xs         = fmap (fromCore a) xs

eqU :: SUTy a -> UVal a -> UVal a -> Bool
eqU SUUnit       ()         ()         = True
eqU SUNat        x          y          = x == y
eqU (SUProd a b) (x1, y1)   (x2, y2)   = eqU a x1 x2 && eqU b y1 y2
eqU (SUSum a _)  (Left x)   (Left y)   = eqU a x y
eqU (SUSum _ b)  (Right x)  (Right y)  = eqU b x y
eqU (SUSum _ _)  _          _          = False
eqU (SUList a)   xs         ys         =
  length xs == length ys && and (zipWith (eqU a) xs ys)

directParity :: SUTy a -> SUTy b -> UMorph a b -> UVal a -> Bool
directParity sa sb f input = case compileDirect f of
  Left _     -> False
  Right core ->
    eqU sb (fromCore sb (evalV core (toCore sa input))) (evalU f input)
      && erasureMatches f == Right True

directError :: UMorph a b -> Maybe DirectError
directError f = case compileDirect f of
  Left err -> Just err
  Right _  -> Nothing

isZeroU :: UMorph 'UNat ('UUnit ':++: 'UUnit)
isZeroU = UCase UInl (UInr :..: UWeak) :..: UNatOut

predU :: UMorph 'UNat 'UNat
predU = UCase (UConst 0) UId :..: UNatOut

positiveU :: UMorph 'UNat ('UNat ':++: 'UUnit)
positiveU = UGuard SUNat (UCase UInr (UInl :..: UWeak) :..: UNatOut)

surfaceVectors :: [(String, Bool)]
surfaceVectors =
  [ ("surface-id", directParity SUNat SUNat UId 4)
  , ("surface-compose", directParity SUNat SUNat (USuc :..: USuc) 4)
  , ("surface-tensor", directParity
      (SUProd SUNat SUNat) (SUProd SUNat SUUnit)
      (USuc :****: UWeak) (4, 7))
  , ("surface-dup-nat", directParity
      SUNat (SUProd SUNat SUNat) (UDup SUNat) 4)
  , ("surface-swap", directParity
      (SUProd SUNat SUUnit) (SUProd SUUnit SUNat) USwap (4, ()))
  , ("surface-assoc", directParity
      (SUProd (SUProd SUNat SUNat) SUNat)
      (SUProd SUNat (SUProd SUNat SUNat)) UAssoc ((1, 2), 3))
  , ("surface-unassoc", directParity
      (SUProd SUNat (SUProd SUNat SUNat))
      (SUProd (SUProd SUNat SUNat) SUNat) UUnassoc (1, (2, 3)))
  , ("surface-exl", directParity
      (SUProd SUNat SUUnit) SUNat UExl (4, ()))
  , ("surface-exr", directParity
      (SUProd SUUnit SUNat) SUNat UExr ((), 4))
  , ("surface-weak", directParity SUNat SUUnit UWeak 4)
  , ("surface-runit", directParity SUNat (SUProd SUNat SUUnit) URunit 4)
  , ("surface-lunit", directParity SUNat (SUProd SUUnit SUNat) ULunit 4)
  , ("surface-inl", directParity
      SUNat (SUSum SUNat SUUnit) UInl 4)
  , ("surface-inr", directParity
      SUUnit (SUSum SUNat SUUnit) UInr ())
  , ("surface-case-left", directParity
      (SUSum SUNat SUUnit) SUNat (UCase USuc (UConst 0)) (Left 4))
  , ("surface-case-right", directParity
      (SUSum SUNat SUUnit) SUNat (UCase USuc (UConst 0)) (Right ()))
  , ("surface-distl-left", directParity
      (SUProd SUNat (SUSum SUNat SUUnit))
      (SUSum (SUProd SUNat SUNat) (SUProd SUNat SUUnit))
      UDistl (4, Left 7))
  , ("surface-distl-right", directParity
      (SUProd SUNat (SUSum SUNat SUUnit))
      (SUSum (SUProd SUNat SUNat) (SUProd SUNat SUUnit))
      UDistl (4, Right ()))
  , ("surface-nil", directParity SUUnit (SUList SUNat) UNil ())
  , ("surface-cons", directParity
      (SUProd SUNat (SUList SUNat)) (SUList SUNat) UCons (1, [2, 3]))
  , ("surface-uncons-empty", directParity
      (SUList SUNat) (SUSum SUUnit (SUProd SUNat (SUList SUNat)))
      UUncons [])
  , ("surface-uncons-nonempty", directParity
      (SUList SUNat) (SUSum SUUnit (SUProd SUNat (SUList SUNat)))
      UUncons [1, 2])
  , ("surface-natout-zero", directParity
      SUNat (SUSum SUUnit SUNat) UNatOut 0)
  , ("surface-natout-suc", directParity
      SUNat (SUSum SUUnit SUNat) UNatOut 4)
  , ("surface-suc", directParity SUNat SUNat USuc 4)
  , ("surface-add", directParity
      (SUProd SUNat SUNat) SUNat UAdd (4, 7))
  , ("surface-const", directParity SUUnit SUNat (UConst 9) ())
  , ("surface-guard-pass", directParity
      SUNat (SUSum SUNat SUUnit) positiveU 4)
  , ("surface-guard-fail", directParity
      SUNat (SUSum SUNat SUUnit) positiveU 0)
  , ("surface-reject-general-dup",
      directError (UDup (SUProd SUNat SUNat)) == Just GeneralDuplication)
  , ("surface-reject-iter",
      directError (UIter USuc) == Just (RecursionRequiresPlacement Iteration))
  , ("surface-reject-fold",
      directError (UFold UAdd) == Just (RecursionRequiresPlacement Fold))
  , ("surface-reject-while",
      directError (UWhile SUNat isZeroU predU)
        == Just (RecursionRequiresPlacement While))
  , ("surface-iter-semantics", evalU (UIter USuc) (3, 2) == 5)
  , ("surface-fold-semantics", evalU (UFold UAdd) ([1, 2, 3], 0) == 6)
  , ("surface-while-semantics",
      evalU (UWhile SUNat isZeroU predU) (5, 3) == 0)
  ]
