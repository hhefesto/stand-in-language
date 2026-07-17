{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module TransportVectors (constructorNodes, transportVectors) where

import Data.Either (isLeft, isRight)

import Telomare.Core
import Telomare.Transport

allConstructors :: Morph ('Nat ':*: 'Bang 'Nat) ('Bang 'Nat)
allConstructors = WhileS SNat predicate SucS
  where
    predicate = CaseS InlS (InrS :.: WeakS) :.: NatOutS

constructorNodes :: [Artifact]
constructorNodes =
  [ exportMorph SNat SNat IdS
  , exportMorph SNat SNat (SucS :.: IdS)
  , exportMorph (SProd SNat SUnit) (SProd SNat SUnit) (IdS :***: IdS)
  , exportMorph (SProd SNat SUnit) (SProd SUnit SNat) SwapS
  , exportMorph (SProd (SProd SNat SUnit) SNat) (SProd SNat (SProd SUnit SNat)) AssocS
  , exportMorph (SProd SNat (SProd SUnit SNat)) (SProd (SProd SNat SUnit) SNat) UnassocS
  , exportMorph (SProd SNat SUnit) SNat ExlS
  , exportMorph (SProd SUnit SNat) SNat ExrS
  , exportMorph SNat SUnit WeakS
  , exportMorph SNat (SProd SNat SUnit) RunitS
  , exportMorph SNat (SProd SUnit SNat) LunitS
  , exportMorph SNat (SSum SNat SUnit) InlS
  , exportMorph SNat (SSum SUnit SNat) InrS
  , exportMorph (SSum SNat SNat) SNat (CaseS IdS IdS)
  , exportMorph (SProd SNat (SSum SUnit SNat)) (SSum (SProd SNat SUnit) (SProd SNat SNat)) DistlS
  , exportMorph SUnit (SList SNat) NilS
  , exportMorph (SProd SNat (SList SNat)) (SList SNat) ConsS
  , exportMorph (SList SNat) (SSum SUnit (SProd SNat (SList SNat))) UnconsS
  , exportMorph SNat (SSum SUnit SNat) NatOutS
  , exportMorph SNat SNat SucS
  , exportMorph (SProd SNat SNat) SNat AddS
  , exportMorph SUnit SNat (ConstS 7)
  , exportMorph SNat (SProd SNat SNat) DupNatS
  , exportMorph (SList SNat) (SProd (SList SNat) (SList SNat))
      (CopyS (CopyList CopyNat))
  , exportMorph (SSum SUnit SNat) (SProd (SSum SUnit SNat) (SSum SUnit SNat))
      (CopyS (CopySum CopyUnit CopyNat))
  , exportMorph SNat (SSum SNat SUnit) (GuardS SNat (CaseS InlS (InrS :.: WeakS) :.: NatOutS))
  , exportMorph (SBang SNat) (SProd (SBang SNat) (SBang SNat)) (DupS SNat)
  , exportMorph (SBang SNat) (SBang SNat) (BoxS SucS)
  , exportMorph SUnit (SBang SNat) (BoxValS (ConstS 1))
  , exportMorph (SProd (SBang SNat) (SBang SUnit)) (SBang (SProd SNat SUnit)) MergeS
  , exportMorph (SList SNat) (SBang (SList SNat)) (MapS SucS)
  , exportMorph (SProd SNat (SBang SNat)) (SBang SNat) (IterS SucS)
  , exportMorph (SProd (SList SNat) (SBang SNat)) (SBang SNat) (FoldS AddS)
  , exportMorph (SProd SNat (SBang SNat)) (SBang SNat) allConstructors
  ]

transportVectors :: [(String, Bool)]
transportVectors =
  [ ("transport-constructor-coverage", all (isRight . validateArtifact) constructorNodes)
  , ("transport-round-trip", all roundTrips constructorNodes)
  , ("transport-version-rejected", isLeft (validateArtifact (Artifact (transportVersion + 1) TNat TNat NId)))
  , ("transport-top-endpoint-rejected", isLeft (validateArtifact (Artifact transportVersion TUnit TNat NSuc)))
  , ("transport-compose-intermediate-rejected", isLeft (validateArtifact (Artifact transportVersion TNat TNat (NCompose NSuc NNil))))
  , ("transport-box-val-unit-rejected", isLeft (validateArtifact (Artifact transportVersion TUnit (TBang TNat) (NBoxVal NSuc))))
  , ("transport-dup-bang-rejected", isLeft (validateArtifact (Artifact transportVersion TNat (TProd TNat TNat) (NDup TNat))))
  , ("transport-copy-endpoint-rejected", isLeft (validateArtifact (Artifact transportVersion (TList TNat) (TList TNat) (NCopy (TList TNat)))))
  , ("transport-copy-mismatch-rejected", isLeft (validateArtifact (Artifact transportVersion TNat (TProd TNat TNat) (NCopy (TList TNat)))))
  , ("transport-merge-shape-rejected", isLeft (validateArtifact (Artifact transportVersion (TProd TNat TNat) (TBang (TProd TNat TNat)) NMerge)))
  , ("transport-map-shape-rejected", isLeft (validateArtifact (Artifact transportVersion (TList TNat) (TList TNat) (NMap NSuc))))
  , ("transport-iter-body-rejected", isLeft (validateArtifact (Artifact transportVersion (TProd TNat (TBang TNat)) (TBang TNat) (NIter NNatOut))))
  , ("transport-fold-body-rejected", isLeft (validateArtifact (Artifact transportVersion (TProd (TList TNat) (TBang TNat)) (TBang TNat) (NFold NSuc))))
  , ("transport-while-body-rejected", isLeft (validateArtifact (Artifact transportVersion (TProd TNat (TBang TNat)) (TBang TNat) (NWhile TNat NSuc NSuc))))
  , ("transport-parser-rejects-show", isLeft (parseArtifact (show (head constructorNodes))))
  ]
  where
    roundTrips artifact = parseArtifact (renderArtifact artifact) == Right artifact
