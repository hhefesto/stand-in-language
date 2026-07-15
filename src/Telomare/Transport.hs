{-# LANGUAGE GADTs #-}

-- | Backend-neutral, first-order transport for the trusted typed core.
--
-- 'Morph' remains the trusted producer.  Consumers must parse and then call
-- 'validateArtifact'; neither parsing nor the transport constructors establish
-- typing.  Validation is an independent untyped inference pass and does not
-- reconstruct a 'Morph'.
module Telomare.Transport
  ( TyCode (..)
  , Node (..)
  , Artifact (..)
  , ValidatedArtifact
  , ValidationError (..)
  , ProgramArtifact (..)
  , transportVersion
  , styCode
  , exportMorph
  , exportCoreEntry
  , exportProgram
  , validateArtifact
  , validatedArtifact
  , renderArtifact
  , parseArtifact
  ) where

import Control.Monad (unless, when)
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.State.Strict (StateT, evalStateT, get, put)
import Data.Char (isAlphaNum, isAscii, isDigit, isSpace)
import Data.List (nub)
import Numeric.Natural (Natural)
import Text.ParserCombinators.ReadP hiding (get)

import Telomare.Core
import Telomare.Machine (CoreEntry (..), Program (..))
import Telomare.Surface (liftSTy)

-- | Stable schema version.  A validator accepts exactly this version.
transportVersion :: Int
transportVersion = 1

-- | Runtime representation of every core object, including the exponential.
data TyCode
  = TUnit
  | TNat
  | TProd TyCode TyCode
  | TSum TyCode TyCode
  | TList TyCode
  | TBang TyCode
  deriving (Eq, Ord, Show)

-- | One first-order node for each current 'Morph' constructor.
data Node
  = NId
  | NCompose Node Node
  | NProduct Node Node
  | NSwap
  | NAssoc
  | NUnassoc
  | NExl
  | NExr
  | NWeak
  | NRunit
  | NLunit
  | NInl
  | NInr
  | NCase Node Node
  | NDistl
  | NNil
  | NCons
  | NUncons
  | NNatOut
  | NSuc
  | NAdd
  | NConst Natural
  | NDupNat
  | NGuard TyCode Node
  | NDup TyCode
  | NBox Node
  | NBoxVal Node
  | NMerge
  | NIter Node
  | NFold Node
  | NWhile TyCode Node Node
  deriving (Eq, Show)

-- | A complete morph transport unit.  Endpoints are mandatory because many
-- structural nodes are polymorphic and cannot carry them intrinsically.
data Artifact = Artifact
  { artifactVersion :: Int
  , artifactInput   :: TyCode
  , artifactOutput  :: TyCode
  , artifactNode    :: Node
  }
  deriving (Eq, Show)

newtype ValidatedArtifact = ValidatedArtifact Artifact
  deriving (Eq, Show)

newtype ValidationError = ValidationError { validationMessage :: String }
  deriving (Eq, Show)

-- | Program transport retains the existential state witness as data and both
-- compiled entries.  Surface evaluator terms are deliberately not transported.
data ProgramArtifact = ProgramArtifact
  { programArtifactVersion :: Int
  , programArtifactState   :: TyCode
  , programArtifactInitial :: Artifact
  , programArtifactStep    :: Artifact
  }
  deriving (Eq, Show)

styCode :: STy a -> TyCode
styCode SUnit       = TUnit
styCode SNat        = TNat
styCode (SProd a b) = TProd (styCode a) (styCode b)
styCode (SSum a b)  = TSum (styCode a) (styCode b)
styCode (SList a)   = TList (styCode a)
styCode (SBang a)   = TBang (styCode a)

-- | Export a typed morph when its endpoint witnesses are available.  A bare
-- polymorphic 'Morph' does not retain enough evidence to recover these types.
exportMorph :: STy a -> STy b -> Morph a b -> Artifact
exportMorph input output morph =
  Artifact transportVersion (styCode input) (styCode output) (exportNode morph)

exportCoreEntry :: CoreEntry a b -> Artifact
exportCoreEntry (CoreEntry input output _ morph) =
  exportMorph (liftSTy input) output morph

exportProgram :: Program -> ProgramArtifact
exportProgram (Program state _ _ initial step) = ProgramArtifact
  { programArtifactVersion = transportVersion
  , programArtifactState = styCode (liftSTy state)
  , programArtifactInitial = exportCoreEntry initial
  , programArtifactStep = exportCoreEntry step
  }

exportNode :: Morph a b -> Node
exportNode IdS            = NId
exportNode (g :.: f)      = NCompose (exportNode g) (exportNode f)
exportNode (f :***: g)    = NProduct (exportNode f) (exportNode g)
exportNode SwapS          = NSwap
exportNode AssocS         = NAssoc
exportNode UnassocS       = NUnassoc
exportNode ExlS           = NExl
exportNode ExrS           = NExr
exportNode WeakS          = NWeak
exportNode RunitS         = NRunit
exportNode LunitS         = NLunit
exportNode InlS           = NInl
exportNode InrS           = NInr
exportNode (CaseS l r)    = NCase (exportNode l) (exportNode r)
exportNode DistlS         = NDistl
exportNode NilS           = NNil
exportNode ConsS          = NCons
exportNode UnconsS        = NUncons
exportNode NatOutS        = NNatOut
exportNode SucS           = NSuc
exportNode AddS           = NAdd
exportNode (ConstS n)     = NConst n
exportNode DupNatS        = NDupNat
exportNode (GuardS a t)   = NGuard (styCode a) (exportNode t)
exportNode (DupS a)       = NDup (styCode a)
exportNode (BoxS f)       = NBox (exportNode f)
exportNode (BoxValS f)    = NBoxVal (exportNode f)
exportNode MergeS         = NMerge
exportNode (IterS f)      = NIter (exportNode f)
exportNode (FoldS f)      = NFold (exportNode f)
exportNode (WhileS a t s) = NWhile (styCode a) (exportNode t) (exportNode s)

data IType
  = IVar Int
  | IUnit
  | INat
  | IProd IType IType
  | ISum IType IType
  | IList IType
  | IBang IType
  deriving (Eq, Show)

data InferState = InferState
  { inferNext  :: Int
  , inferSubst :: [(Int, IType)]
  }

type Infer = StateT InferState (Except ValidationError)

validateArtifact :: Artifact -> Either ValidationError ValidatedArtifact
validateArtifact artifact
  | artifactVersion artifact /= transportVersion =
      Left (ValidationError ("unsupported transport version " <> show (artifactVersion artifact)))
  | otherwise = runExcept $ evalStateT check (InferState 0 [])
  where
    check = do
      (input, output) <- inferNode (artifactNode artifact)
      unify "top input" input (fromCode (artifactInput artifact))
      unify "top output" output (fromCode (artifactOutput artifact))
      pure (ValidatedArtifact artifact)

validatedArtifact :: ValidatedArtifact -> Artifact
validatedArtifact (ValidatedArtifact artifact) = artifact

fresh :: Infer IType
fresh = do
  state <- get
  put state { inferNext = inferNext state + 1 }
  pure (IVar (inferNext state))

fromCode :: TyCode -> IType
fromCode TUnit       = IUnit
fromCode TNat        = INat
fromCode (TProd a b) = IProd (fromCode a) (fromCode b)
fromCode (TSum a b)  = ISum (fromCode a) (fromCode b)
fromCode (TList a)   = IList (fromCode a)
fromCode (TBang a)   = IBang (fromCode a)

prune :: IType -> Infer IType
prune ty@(IVar variable) = do
  substitutions <- inferSubst <$> get
  case lookup variable substitutions of
    Nothing -> pure ty
    Just replacement -> do
      resolved <- prune replacement
      state <- get
      put state { inferSubst = (variable, resolved) : inferSubst state }
      pure resolved
prune ty = pure ty

occurs :: Int -> IType -> Infer Bool
occurs variable ty = do
  resolved <- prune ty
  case resolved of
    IVar other   -> pure (variable == other)
    IProd a b    -> (||) <$> occurs variable a <*> occurs variable b
    ISum a b     -> (||) <$> occurs variable a <*> occurs variable b
    IList a      -> occurs variable a
    IBang a      -> occurs variable a
    IUnit        -> pure False
    INat         -> pure False

unify :: String -> IType -> IType -> Infer ()
unify context left right = do
  a <- prune left
  b <- prune right
  case (a, b) of
    (IVar x, IVar y) | x == y -> pure ()
    (IVar x, ty) -> bind x ty
    (ty, IVar x) -> bind x ty
    (IUnit, IUnit) -> pure ()
    (INat, INat) -> pure ()
    (IProd a1 a2, IProd b1 b2) -> unify context a1 b1 >> unify context a2 b2
    (ISum a1 a2, ISum b1 b2) -> unify context a1 b1 >> unify context a2 b2
    (IList x, IList y) -> unify context x y
    (IBang x, IBang y) -> unify context x y
    _ -> failValidation (context <> ": cannot unify " <> show a <> " with " <> show b)
  where
    bind variable ty = do
      recursive <- occurs variable ty
      when recursive (failValidation (context <> ": infinite type"))
      state <- get
      put state { inferSubst = (variable, ty) : inferSubst state }

failValidation :: String -> Infer a
failValidation = throwError . ValidationError

inferNode :: Node -> Infer (IType, IType)
inferNode node = case node of
  NId -> do a <- fresh; pure (a, a)
  NCompose g f -> do
    (fi, fo) <- inferNode f
    (gi, go) <- inferNode g
    unify "compose intermediate" fo gi
    pure (fi, go)
  NProduct f g -> do
    (fi, fo) <- inferNode f
    (gi, go) <- inferNode g
    pure (IProd fi gi, IProd fo go)
  NSwap -> do a <- fresh; b <- fresh; pure (IProd a b, IProd b a)
  NAssoc -> do a <- fresh; b <- fresh; c <- fresh; pure (IProd (IProd a b) c, IProd a (IProd b c))
  NUnassoc -> do a <- fresh; b <- fresh; c <- fresh; pure (IProd a (IProd b c), IProd (IProd a b) c)
  NExl -> do a <- fresh; b <- fresh; pure (IProd a b, a)
  NExr -> do a <- fresh; b <- fresh; pure (IProd a b, b)
  NWeak -> do a <- fresh; pure (a, IUnit)
  NRunit -> do a <- fresh; pure (a, IProd a IUnit)
  NLunit -> do a <- fresh; pure (a, IProd IUnit a)
  NInl -> do a <- fresh; b <- fresh; pure (a, ISum a b)
  NInr -> do a <- fresh; b <- fresh; pure (b, ISum a b)
  NCase l r -> do
    (li, lo) <- inferNode l
    (ri, ro) <- inferNode r
    unify "case branch output" lo ro
    pure (ISum li ri, lo)
  NDistl -> do a <- fresh; b <- fresh; c <- fresh; pure (IProd a (ISum b c), ISum (IProd a b) (IProd a c))
  NNil -> do a <- fresh; pure (IUnit, IList a)
  NCons -> do a <- fresh; pure (IProd a (IList a), IList a)
  NUncons -> do a <- fresh; pure (IList a, ISum IUnit (IProd a (IList a)))
  NNatOut -> pure (INat, ISum IUnit INat)
  NSuc -> pure (INat, INat)
  NAdd -> pure (IProd INat INat, INat)
  NConst _ -> do a <- fresh; pure (a, INat)
  NDupNat -> pure (INat, IProd INat INat)
  NGuard witness test -> do
    let a = fromCode witness
    (ti, to) <- inferNode test
    unify "guard input" ti a
    unify "guard predicate" to (ISum IUnit IUnit)
    pure (a, ISum a IUnit)
  NDup witness -> let a = fromCode witness in pure (IBang a, IProd (IBang a) (IBang a))
  NBox body -> do
    (input, output) <- inferNode body
    pure (IBang input, IBang output)
  NBoxVal body -> do
    (input, output) <- inferNode body
    unify "box-val input" input IUnit
    pure (IUnit, IBang output)
  NMerge -> do a <- fresh; b <- fresh; pure (IProd (IBang a) (IBang b), IBang (IProd a b))
  NIter body -> do
    (input, output) <- inferNode body
    unify "iter body" input output
    pure (IProd INat (IBang input), IBang input)
  NFold body -> do
    element <- fresh
    accumulator <- fresh
    (input, output) <- inferNode body
    unify "fold body input" input (IProd accumulator element)
    unify "fold body output" output accumulator
    pure (IProd (IList element) (IBang accumulator), IBang accumulator)
  NWhile witness test step -> do
    let a = fromCode witness
    (ti, to) <- inferNode test
    (si, so) <- inferNode step
    unify "while predicate input" ti a
    unify "while predicate output" to (ISum IUnit IUnit)
    unify "while step input" si a
    unify "while step output" so a
    pure (IProd INat (IBang a), IBang a)

-- | Canonical whitespace-free S-expression wire format.
renderArtifact :: Artifact -> String
renderArtifact (Artifact version input output node) =
  list ["morph", show version, renderType input, renderType output, renderNode node]

renderType :: TyCode -> String
renderType TUnit       = "unit"
renderType TNat        = "nat"
renderType (TProd a b) = list ["prod", renderType a, renderType b]
renderType (TSum a b)  = list ["sum", renderType a, renderType b]
renderType (TList a)   = list ["list", renderType a]
renderType (TBang a)   = list ["bang", renderType a]

renderNode :: Node -> String
renderNode node = case node of
  NId -> atom "id"; NCompose g f -> pair "compose" g f; NProduct f g -> pair "product" f g
  NSwap -> atom "swap"; NAssoc -> atom "assoc"; NUnassoc -> atom "unassoc"
  NExl -> atom "exl"; NExr -> atom "exr"; NWeak -> atom "weak"
  NRunit -> atom "runit"; NLunit -> atom "lunit"; NInl -> atom "inl"; NInr -> atom "inr"
  NCase l r -> pair "case" l r; NDistl -> atom "distl"; NNil -> atom "nil"
  NCons -> atom "cons"; NUncons -> atom "uncons"; NNatOut -> atom "nat-out"
  NSuc -> atom "suc"; NAdd -> atom "add"; NConst n -> list ["const", show n]
  NDupNat -> atom "dup-nat"; NGuard ty test -> list ["guard", renderType ty, renderNode test]
  NDup ty -> list ["dup", renderType ty]; NBox body -> unary "box" body
  NBoxVal body -> unary "box-val" body; NMerge -> atom "merge"; NIter body -> unary "iter" body
  NFold body -> unary "fold" body
  NWhile ty test step -> list ["while", renderType ty, renderNode test, renderNode step]
  where
    atom name = list [name]
    unary name child = list [name, renderNode child]
    pair name left right = list [name, renderNode left, renderNode right]

list :: [String] -> String
list fields = "(" <> unwords fields <> ")"

parseArtifact :: String -> Either String Artifact
parseArtifact source = case nub [value | (value, "") <- readP_to_S (spaces *> artifactP <* spaces <* eof) source] of
  [artifact] -> Right artifact
  _          -> Left "invalid transport artifact"

artifactP :: ReadP Artifact
artifactP = parens $ do
  _ <- symbol "morph"
  version <- naturalP
  when (version > fromIntegral (maxBound :: Int)) pfail
  Artifact (fromIntegral version) <$> typeP <*> typeP <*> nodeP

typeP :: ReadP TyCode
typeP =
      (symbol "unit" >> pure TUnit)
  +++ (symbol "nat" >> pure TNat)
  +++ parens ((symbol "prod" >> TProd <$> typeP <*> typeP)
          +++ (symbol "sum" >> TSum <$> typeP <*> typeP)
          +++ (symbol "list" >> TList <$> typeP)
          +++ (symbol "bang" >> TBang <$> typeP))

nodeP :: ReadP Node
nodeP = parens $ choice
  [ nullary "id" NId, binary "compose" NCompose, binary "product" NProduct
  , nullary "swap" NSwap, nullary "assoc" NAssoc, nullary "unassoc" NUnassoc
  , nullary "exl" NExl, nullary "exr" NExr, nullary "weak" NWeak
  , nullary "runit" NRunit, nullary "lunit" NLunit, nullary "inl" NInl
  , nullary "inr" NInr, binary "case" NCase, nullary "distl" NDistl
  , nullary "nil" NNil, nullary "cons" NCons, nullary "uncons" NUncons
  , nullary "nat-out" NNatOut, nullary "suc" NSuc, nullary "add" NAdd
  , symbol "const" >> NConst <$> naturalP, nullary "dup-nat" NDupNat
  , symbol "guard" >> NGuard <$> typeP <*> nodeP, symbol "dup" >> NDup <$> typeP
  , unary "box" NBox, unary "box-val" NBoxVal, nullary "merge" NMerge
  , unary "iter" NIter, unary "fold" NFold
  , symbol "while" >> NWhile <$> typeP <*> nodeP <*> nodeP
  ]
  where
    nullary name value = symbol name >> pure value
    unary name constructor = symbol name >> constructor <$> nodeP
    binary name constructor = symbol name >> constructor <$> nodeP <*> nodeP

parens :: ReadP a -> ReadP a
parens parser = token (char '(') *> parser <* token (char ')')

symbol :: String -> ReadP String
symbol expected = token $ do
  actual <- munch1 (\character -> isAlphaNum character || character == '-')
  unless (actual == expected) pfail
  pure actual

naturalP :: ReadP Natural
naturalP = token (read <$> munch1 (\character -> isAscii character && isDigit character))

token :: ReadP a -> ReadP a
token parser = parser <* spaces

spaces :: ReadP ()
spaces = skipMany (satisfy isSpace)
