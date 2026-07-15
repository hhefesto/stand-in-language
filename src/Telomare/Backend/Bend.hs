-- | Direct first-order Bend source generation from validated core transport.
--
-- This is deliberately a value-only prototype. It does not preserve or report
-- work, fuel, or duplication grades, and transparent boxes are metadata rather
-- than evidence that Bend or HVM enforces EAL.
module Telomare.Backend.Bend
  ( BendError (..)
  , bendU24Max
  , emitBend
  ) where

import Control.Monad.State.Strict (State, get, put, runState)
import Numeric.Natural (Natural)

import Telomare.Transport

newtype BendError = BendError { bendErrorMessage :: String }
  deriving (Eq, Show)

-- | Largest natural represented exactly by the prototype's Bend @u24@ scalar.
bendU24Max :: Natural
bendU24Max = 16777215

data EmitState = EmitState
  { emitNext :: Int
  , emitDefs :: [String]
  }

-- | Emit a self-contained Bend program. The only accepted compiler input is an
-- opaque 'ValidatedArtifact'; parsing and type checking stay outside this
-- backend.
emitBend :: ValidatedArtifact -> Either BendError String
emitBend validated = do
  rejectLargeConstants (artifactNode artifact)
  let (root, definitions) = runEmitter (emitNode (artifactNode artifact))
      inputChecks = emitChecks (artifactInput artifact)
  pure (unlines (preamble artifact <> inputChecks <> definitions <> emitRun root))
  where
    artifact = validatedArtifact validated

runEmitter :: State EmitState String -> (String, [String])
runEmitter action =
  let (root, final) = runState action (EmitState 0 [])
  in (root, reverse (emitDefs final))

freshName :: String -> State EmitState String
freshName prefix = do
  state <- get
  put state { emitNext = emitNext state + 1 }
  pure (prefix <> show (emitNext state))

addDef :: String -> State EmitState ()
addDef definition = do
  state <- get
  put state { emitDefs = definition : emitDefs state }

define :: String -> [String] -> State EmitState String
define constructor body = do
  name <- freshName "node_"
  addDef (unlines
    (("# " <> constructor) :
     ("def " <> name <> "(x):") :
     "  match x:" :
     "    case Value/DomainError:" :
     "      return x" :
     "    case _:" :
     fmap ("      " <>) body))
  pure name

emitNode :: Node -> State EmitState String
emitNode node = case node of
  NId -> define "NId" ["return x"]
  NCompose g f -> do
    fName <- emitNode f
    gName <- emitNode g
    define "NCompose" ["return " <> gName <> "(" <> fName <> "(x))"]
  NProduct f g -> do
    fName <- emitNode f
    gName <- emitNode g
    define "NProduct" (propagatePair
      (fName <> "(value_fst(x))") (gName <> "(value_snd(x))"))
  NSwap -> define "NSwap"
    ["return Value/Prod(value_snd(x), value_fst(x))"]
  NAssoc -> define "NAssoc"
    ["return Value/Prod(value_fst(value_fst(x)), Value/Prod(value_snd(value_fst(x)), value_snd(x)))"]
  NUnassoc -> define "NUnassoc"
    ["return Value/Prod(Value/Prod(value_fst(x), value_fst(value_snd(x))), value_snd(value_snd(x)))"]
  NExl -> define "NExl" ["return value_fst(x)"]
  NExr -> define "NExr" ["return value_snd(x)"]
  NWeak -> define "NWeak" ["return Value/Unit"]
  NRunit -> define "NRunit" ["return Value/Prod(x, Value/Unit)"]
  NLunit -> define "NLunit" ["return Value/Prod(Value/Unit, x)"]
  NInl -> define "NInl" ["return Value/Inl(x)"]
  NInr -> define "NInr" ["return Value/Inr(x)"]
  NCase l r -> do
    lName <- emitNode l
    rName <- emitNode r
    define "NCase"
      [ "match x:"
      , "  case Value/Inl:"
      , "    return " <> lName <> "(x.value)"
      , "  case Value/Inr:"
      , "    return " <> rName <> "(x.value)"
      , "  case Value/DomainError:"
      , "    return x"
      , "  case _:"
      , "    return Value/DomainError"
      ]
  NDistl -> define "NDistl"
    [ "match value_snd(x):"
    , "  case Value/Inl:"
    , "    return Value/Inl(Value/Prod(value_fst(x), value_payload(value_snd(x))))"
    , "  case Value/Inr:"
    , "    return Value/Inr(Value/Prod(value_fst(x), value_payload(value_snd(x))))"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NNil -> define "NNil" ["return Value/Nil"]
  NCons -> define "NCons" ["return Value/Cons(value_fst(x), value_snd(x))"]
  NUncons -> define "NUncons"
    [ "match x:"
    , "  case Value/Nil:"
    , "    return Value/Inl(Value/Unit)"
    , "  case Value/Cons:"
    , "    return Value/Inr(Value/Prod(x.head, x.tail))"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NNatOut -> define "NNatOut"
    [ "match x:"
    , "  case Value/Nat:"
    , "    switch x.value:"
    , "      case 0:"
    , "        return Value/Inl(Value/Unit)"
    , "      case _:"
    , "        return Value/Inr(Value/Nat(x.value - 1))"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NSuc -> define "NSuc"
    [ "match x:"
    , "  case Value/Nat:"
    , "    switch x.value == 16777215:"
    , "      case 0:"
    , "        return Value/Nat(x.value + 1)"
    , "      case _:"
    , "        return Value/DomainError"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NAdd -> define "NAdd"
    [ "left_value = value_fst(x)"
    , "match left_value:"
    , "  case Value/Nat:"
    , "    left = left_value.value"
    , "    right_value = value_snd(x)"
    , "    match right_value:"
    , "      case Value/Nat:"
    , "        right = right_value.value"
    , "        switch left > 16777215 - right:"
    , "          case 0:"
    , "            return Value/Nat(left + right)"
    , "          case _:"
    , "            return Value/DomainError"
    , "      case _:"
    , "        return Value/DomainError"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NConst n -> define ("NConst " <> show n) ["return Value/Nat(" <> show n <> ")"]
  NDupNat -> define "NDupNat"
    [ "match x:"
    , "  case Value/Nat:"
    , "    return Value/Prod(Value/Nat(x.value), Value/Nat(x.value))"
    , "  case _:"
    , "    return Value/DomainError"
    ]
  NGuard witness test -> do
    testName <- emitNode test
    define ("NGuard " <> renderTy witness)
      [ "result = " <> testName <> "(x)"
      , "match result:"
      , "  case Value/Inl:"
      , "    return Value/Inl(x)"
      , "  case Value/Inr:"
      , "    return Value/Inr(Value/Unit)"
      , "  case Value/DomainError:"
      , "    return result"
      , "  case _:"
      , "    return Value/DomainError"
      ]
  NDup witness -> define ("NDup " <> renderTy witness <> " (value-only duplication; no grade claim)")
    ["return Value/Prod(x, x)"]
  NBox body -> do
    bodyName <- emitNode body
    define "NBox (value-transparent metadata; no EAL enforcement claim)" ["return " <> bodyName <> "(x)"]
  NBoxVal body -> do
    bodyName <- emitNode body
    define "NBoxVal (value-transparent metadata; no EAL enforcement claim)" ["return " <> bodyName <> "(x)"]
  NMerge -> define "NMerge (value-transparent boxes)"
    ["return Value/Prod(value_fst(x), value_snd(x))"]
  NIter body -> emitIter body
  NFold body -> emitFold body
  NWhile witness test step -> emitWhile witness test step

propagatePair :: String -> String -> [String]
propagatePair left right =
  [ "left = " <> left
  , "match left:"
  , "  case Value/DomainError:"
  , "    return left"
  , "  case _:"
  , "    right = " <> right
  , "    match right:"
  , "      case Value/DomainError:"
  , "        return right"
  , "      case _:"
  , "        return Value/Prod(left, right)"
  ]

emitIter :: Node -> State EmitState String
emitIter body = do
  bodyName <- emitNode body
  loopName <- freshName "iter_"
  addDef (unlines
    [ "# NIter helper: exactly n body calls, seed remains second"
    , "def " <> loopName <> "(n, state):"
    , "  switch n:"
    , "    case 0:"
    , "      return state"
    , "    case _:"
    , "      next = " <> bodyName <> "(state)"
    , "      match next:"
    , "        case Value/DomainError:"
    , "          return next"
    , "        case _:"
    , "          return " <> loopName <> "(n - 1, next)"
    ])
  define "NIter (bounded by first input; value order is (count, seed))"
    [ "fuel = value_fst(x)"
    , "match fuel:"
    , "  case Value/Nat:"
    , "    return " <> loopName <> "(fuel.value, value_snd(x))"
    , "  case _:"
    , "    return Value/DomainError"
    ]

emitFold :: Node -> State EmitState String
emitFold body = do
  bodyName <- emitNode body
  loopName <- freshName "fold_"
  addDef (unlines
    [ "# NFold helper: head-to-tail, body input is (accumulator, element)"
    , "def " <> loopName <> "(list, accumulator):"
    , "  match list:"
    , "    case Value/Nil:"
    , "      return accumulator"
    , "    case Value/Cons:"
    , "      next = " <> bodyName <> "(Value/Prod(accumulator, list.head))"
    , "      match next:"
    , "        case Value/DomainError:"
    , "          return next"
    , "        case _:"
    , "          return " <> loopName <> "(list.tail, next)"
    , "    case _:"
    , "      return Value/DomainError"
    ])
  define "NFold (value order is (list, seed))"
    ["return " <> loopName <> "(value_fst(x), value_snd(x))"]

emitWhile :: TyCode -> Node -> Node -> State EmitState String
emitWhile witness test step = do
  testName <- emitNode test
  stepName <- emitNode step
  loopName <- freshName "while_"
  addDef (unlines
    [ "# NWhile helper: bounded pre-test; Inl stops and Inr steps"
    , "def " <> loopName <> "(n, state):"
    , "  switch n:"
    , "    case 0:"
    , "      return state"
    , "    case _:"
    , "      decision = " <> testName <> "(state)"
    , "      match decision:"
    , "        case Value/Inl:"
    , "          return state"
    , "        case Value/Inr:"
    , "          next = " <> stepName <> "(state)"
    , "          match next:"
    , "            case Value/DomainError:"
    , "              return next"
    , "            case _:"
    , "              return " <> loopName <> "(n - 1, next)"
    , "        case Value/DomainError:"
    , "          return decision"
    , "        case _:"
    , "          return Value/DomainError"
    ])
  define ("NWhile " <> renderTy witness <> " (value order is (limit, seed))")
    [ "fuel = value_fst(x)"
    , "match fuel:"
    , "  case Value/Nat:"
    , "    return " <> loopName <> "(fuel.value, value_snd(x))"
    , "  case _:"
    , "    return Value/DomainError"
    ]

rejectLargeConstants :: Node -> Either BendError ()
rejectLargeConstants node = case node of
  NConst n | n > bendU24Max -> Left (BendError
    ("constant " <> show n <> " exceeds checked Bend u24 domain 0.." <> show bendU24Max))
  NCompose a b -> both a b
  NProduct a b -> both a b
  NCase a b -> both a b
  NGuard _ a -> rejectLargeConstants a
  NBox a -> rejectLargeConstants a
  NBoxVal a -> rejectLargeConstants a
  NIter a -> rejectLargeConstants a
  NFold a -> rejectLargeConstants a
  NWhile _ a b -> both a b
  _ -> Right ()
  where
    both a b = rejectLargeConstants a >> rejectLargeConstants b

preamble :: Artifact -> [String]
preamble artifact =
  [ "# Generated directly from Telomare.Transport.ValidatedArtifact."
  , "# Value semantics only: no work, fuel, duplication-grade, or EAL claim."
  , "# Nat prototype domain: exact Bend u24 values 0..16777215."
  , "# Suc/Add detect overflow; larger constants are rejected before emission."
  , "# Input: " <> renderTy (artifactInput artifact)
  , "# Output: " <> renderTy (artifactOutput artifact)
  , "type Value:"
  , "  Unit"
  , "  Nat { value }"
  , "  Prod { fst, snd }"
  , "  Inl { value }"
  , "  Inr { value }"
  , "  Nil"
  , "  Cons { head, tail }"
  , "  DomainError"
  , "type Run:"
  , "  Ok { value }"
  , "  InvalidInput"
  , "  DomainError"
  , ""
  , "# Dynamic accessors keep generated first-order functions total on bad tags."
  , "def value_fst(x):"
  , "  match x:"
  , "    case Value/Prod:"
  , "      return x.fst"
  , "    case Value/DomainError:"
  , "      return x"
  , "    case _:"
  , "      return Value/DomainError"
  , ""
  , "def value_snd(x):"
  , "  match x:"
  , "    case Value/Prod:"
  , "      return x.snd"
  , "    case Value/DomainError:"
  , "      return x"
  , "    case _:"
  , "      return Value/DomainError"
  , ""
  , "def value_payload(x):"
  , "  match x:"
  , "    case Value/Inl:"
  , "      return x.value"
  , "    case Value/Inr:"
  , "      return x.value"
  , "    case Value/DomainError:"
  , "      return x"
  , "    case _:"
  , "      return Value/DomainError"
  , ""
  ]

emitChecks :: TyCode -> [String]
emitChecks root = reverse (checkDefs final) <> [""]
  where
    (_, final) = runState (emitCheck root) (CheckState 0 [])

    emitCheck :: TyCode -> State CheckState String
    emitCheck ty = do
      state <- get
      let name = "check_" <> show (checkNext state)
      put state { checkNext = checkNext state + 1 }
      body <- checkBody name ty
      current <- get
      put current { checkDefs = unlines
        (("# encoded input check for " <> renderTy ty) :
         ("def " <> name <> "(x):") : fmap ("  " <>) body) : checkDefs current }
      pure name

    checkBody :: String -> TyCode -> State CheckState [String]
    checkBody self ty = case ty of
      TUnit -> pure (matchCheck "Value/Unit" "return 1")
      TNat -> pure (matchCheck "Value/Nat" "return 1")
      TProd a b -> binary "Value/Prod" "fst" a "snd" b
      TSum a b ->
        do
          leftName <- emitCheck a
          rightName <- emitCheck b
          pure
            [ "match x:"
            , "  case Value/Inl:"
            , "    return " <> leftName <> "(x.value)"
            , "  case Value/Inr:"
            , "    return " <> rightName <> "(x.value)"
            , "  case _:"
            , "    return 0"
            ]
      TList a -> do
        elementName <- emitCheck a
        pure
          [ "match x:"
          , "  case Value/Nil:"
          , "    return 1"
          , "  case Value/Cons:"
          , "    return " <> elementName <> "(x.head) * " <> self <> "(x.tail)"
          , "  case _:"
          , "    return 0"
          ]
      TBang a -> do
        name <- emitCheck a
        pure ["return " <> name <> "(x) # Bang is value-transparent metadata"]

    binary :: String -> String -> TyCode -> String -> TyCode
           -> State CheckState [String]
    binary constructor first a second b = do
      aName <- emitCheck a
      bName <- emitCheck b
      pure
        [ "match x:"
        , "  case " <> constructor <> ":"
        , "    return " <> aName <> "(x." <> first <> ") * " <> bName <> "(x." <> second <> ")"
        , "  case _:"
        , "    return 0"
        ]

    matchCheck constructor success =
      [ "match x:"
      , "  case " <> constructor <> ":"
      , "    " <> success
      , "  case _:"
      , "    return 0"
      ]

data CheckState = CheckState
  { checkNext :: Int
  , checkDefs :: [String]
  }

emitRun :: String -> [String]
emitRun root =
  [ "# Result protocol: Ok(value), InvalidInput, or checked-u24 DomainError."
  , "# Supply a closed zero-argument main that calls telomare_run with encoded input."
  , "def telomare_run(input):"
  , "  switch check_0(input):"
  , "    case 0:"
  , "      return Run/InvalidInput"
  , "    case _:"
  , "      result = " <> root <> "(input)"
  , "      match result:"
  , "        case Value/DomainError:"
  , "          return Run/DomainError"
  , "        case _:"
  , "          return Run/Ok(result)"
  ]

renderTy :: TyCode -> String
renderTy ty = case ty of
  TUnit       -> "Unit"
  TNat        -> "Nat[u24 checked]"
  TProd a b   -> "(" <> renderTy a <> " * " <> renderTy b <> ")"
  TSum a b    -> "(" <> renderTy a <> " + " <> renderTy b <> ")"
  TList a     -> "List " <> parenthesize a
  TBang a     -> "Bang " <> parenthesize a
  where
    parenthesize atom@TUnit = renderTy atom
    parenthesize atom@TNat = renderTy atom
    parenthesize other = "(" <> renderTy other <> ")"
