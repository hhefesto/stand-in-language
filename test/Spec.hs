module Main where

import Control.Applicative (liftA2)
import Debug.Trace
import Data.Char
import SIL
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer
import System.Exit
import Test.QuickCheck
import qualified System.IO.Strict as Strict

data TestIExpr = TestIExpr IExpr

instance Show TestIExpr where
  show (TestIExpr t) = show t

lift1Texpr :: (IExpr -> IExpr) -> TestIExpr -> TestIExpr
lift1Texpr f (TestIExpr x) = TestIExpr $ f x

lift2Texpr :: (IExpr -> IExpr -> IExpr) -> TestIExpr -> TestIExpr -> TestIExpr
lift2Texpr f (TestIExpr a) (TestIExpr b) = TestIExpr $ f a b

instance Arbitrary TestIExpr where
  arbitrary = sized tree where
    tree i = let half = div i 2
                 pure2 = pure . TestIExpr
             in case i of
                  0 -> oneof $ map pure2 [Zero, Var]
                  x -> oneof
                    [ pure2 Zero
                    , pure2 Var
                    , lift2Texpr Pair <$> tree half <*> tree half
                    , lift2Texpr App <$> tree half <*> tree half
                    , lift2Texpr Check <$> tree half <*> tree half
                    , lift1Texpr Gate <$> tree (i - 1)
                    , lift1Texpr PLeft <$> tree (i - 1)
                    , lift1Texpr PRight <$> tree (i - 1)
                    , lift1Texpr Trace <$> tree (i - 1)
                    , lift1Texpr (flip Closure Zero) <$> tree (i - 1)
                    ]
  shrink (TestIExpr x) = case x of
    Zero -> []
    Var -> []
    (Gate x) -> TestIExpr x : (map (lift1Texpr Gate) . shrink $ TestIExpr x)
    (PLeft x) -> TestIExpr x : (map (lift1Texpr PLeft) . shrink $ TestIExpr x)
    (PRight x) -> TestIExpr x : (map (lift1Texpr PRight) . shrink $ TestIExpr x)
    (Trace x) -> TestIExpr x : (map (lift1Texpr Trace) . shrink $ TestIExpr x)
    (Closure c z) ->
      TestIExpr c : (map (lift1Texpr (flip Closure z)) . shrink $ TestIExpr c)
    (Pair a b) -> TestIExpr a : TestIExpr  b :
      [lift2Texpr Pair a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]
    (App c i) -> TestIExpr c : TestIExpr i :
      [lift2Texpr App c' i' | (c', i') <- shrink (TestIExpr c, TestIExpr i)]
    (Check c tc) -> TestIExpr c : TestIExpr tc :
      [lift2Texpr Check c' tc' | (c', tc') <- shrink (TestIExpr c, TestIExpr tc)]

three_succ = App (App (anno (toChurch 3) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (varN 0) Zero)))
             Zero

one_succ = App (App (anno (toChurch 1) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (varN 0) Zero)))
             Zero

two_succ = App (App (anno (toChurch 2) (Pair (Pair Zero Zero) (Pair Zero Zero)))
                  (lam (Pair (varN 0) Zero)))
             Zero

church_type = Pair (Pair Zero Zero) (Pair Zero Zero)

c2d = anno (lam (App (App (varN 0) (lam (Pair (varN 0) Zero))) Zero))
  (Pair church_type Zero)

h2c i =
  let layer recurf i churchf churchbase =
        if i > 0
        then churchf $ recurf (i - 1) churchf churchbase
        -- App v1 (App (App (App v3 (PLeft v2)) v1) v0)
        else churchbase
      stopf i churchf churchbase = churchbase
  in \cf cb -> layer (layer (layer (layer stopf))) i cf cb


{-
h_zipWith a b f =
  let layer recurf zipf a b =
        if a > 0
        then if b > 0
             then Pair (zipf (PLeft a) (PLeft b)) (recurf zipf (PRight a) (PRight b))
             else Zero
        else Zero
      stopf _ _ _ = Zero
  in layer (layer (layer (layer stopf))) a b f

foldr_h =
  let layer recurf f accum l =
        if not $ nil l
        then recurf f (f (PLeft l) accum) (PRight l)
        else accum
-}

map_ =
  -- layer recurf f l = Pair (f (PLeft l)) (recurf f (PRight l))
  let layer = lam (lam (lam
                            (ite (varN 0)
                            (Pair
                             (App (varN 1) (PLeft $ varN 0))
                             (App (App (varN 2) (varN 1))
                              (PRight $ varN 0)))
                            Zero
                            )))
      layerType = Pair (Pair Zero Zero) (Pair Zero Zero)
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = lam (lam Zero)
  in App (App (anno (toChurch 255) fixType) layer) base

foldr_ =
  let layer = lam (lam (lam (lam
                                 (ite (varN 0)
                                 (App (App (App (varN 3) (varN 2))

                                       (App (App (varN 2) (PLeft $ varN 0))
                                            (varN 1)))
                                  (PRight $ varN 0))
                                 (varN 1)
                                 )
                                 )))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
      base = lam (lam (lam Zero)) -- var 0?
  in App (App (anno (toChurch 255) fixType) layer) base

zipWith_ =
  let layer = lam (lam (lam (lam
                                  (ite (varN 1)
                                   (ite (varN 0)
                                    (Pair
                                     (App (App (varN 2) (PLeft $ varN 1))
                                      (PLeft $ varN 0))
                                     (App (App (App (varN 3) (varN 2))
                                           (PRight $ varN 1))
                                      (PRight $ varN 0))
                                    )
                                    Zero)
                                   Zero)
                                 )))
      base = lam (lam (lam Zero))
      layerType = Pair (Pair Zero (Pair Zero Zero)) (Pair Zero (Pair Zero Zero))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (anno (toChurch 255) fixType) layer) base

-- layer recurf i churchf churchbase
-- layer :: (Zero -> baseType) -> Zero -> (baseType -> baseType) -> baseType
--           -> baseType
-- converts plain data type number (0-255) to church numeral
d2c baseType =
  let layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (App (varN 1)
                              (App (App (App (varN 3)
                                   (PLeft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
      layerType = Pair Zero (Pair (Pair baseType baseType) (Pair baseType baseType))
      fixType = Pair (Pair layerType layerType) (Pair layerType layerType)
  in App (App (anno (toChurch 255) fixType) layer) base

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = anno (lam (ite (varN 0) (ite (PLeft (varN 0)) Zero (i2g 1)) Zero)) (Pair Zero Zero)

d_to_equality = anno (lam (lam (ite (varN 1)
                                          (App d_equals_one (App (App (App (d2c Zero) (PLeft $ varN 1)) (lam . PLeft $ varN 0)) (varN 0)))
                                          (ite (varN 0) Zero (i2g 1))
                                         ))) (Pair Zero (Pair Zero Zero))

list_equality =
  let pairs_equal = App (App (App zipWith_ d_to_equality) (varN 0)) (varN 1)
      length_equal = App (App d_to_equality (App list_length (varN 1)))
                     (App list_length (varN 0))
      and_ = lam (lam (ite (varN 1) (varN 0) Zero))
      folded = App (App (App foldr_ and_) (i2g 1)) (Pair length_equal pairs_equal)
  in anno (lam (lam folded)) (Pair Zero (Pair Zero Zero))

list_length = anno (lam (App (App (App foldr_ (lam (lam (Pair (varN 0) Zero))))
                                  Zero)
  (varN 0))) (Pair Zero Zero)

plus_ x y =
  let succ = lam (Pair (varN 0) Zero)
      plus_app = App (App (varN 3) (varN 1)) (App (App (varN 2) (varN 1)) (varN 0))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App (App (anno plus plus_type) x) y

d_plus = anno (lam (lam (App c2d (plus_
                                   (App (d2c Zero) (varN 1))
                                   (App (d2c Zero) (varN 0))
                                   )))) (Pair Zero (Pair Zero Zero))

test_plus0 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) Zero))
test_plus1 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 1)))
test_plus254 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 254)))
test_plus255 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 255)))
test_plus256 = App c2d (plus_
                         (toChurch 3)
                         (App (d2c Zero) (i2g 256)))

one_plus_one =
  let succ = lam (Pair (varN 0) Zero)
      plus_app = App (App (varN 3) (varN 1)) (App (App (varN 2) (varN 1)) (varN 0))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App c2d (App (App (anno plus plus_type) (toChurch 1)) (toChurch 1))

-- m f (n f x)
-- App (App m f) (App (App n f) x)
-- App (App (varN 3) (varN 1)) (App (App (varN 2) (varN 1)) (varN 0))
three_plus_two =
  let succ = lam (Pair (varN 0) Zero)
      plus_app = App (App (varN 3) (varN 1)) (App (App (varN 2) (varN 1)) (varN 0))
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      plus_type = Pair church_type (Pair church_type church_type)
      plus = lam (lam (lam (lam plus_app)))
  in App c2d (App (App (anno plus plus_type) (toChurch 3)) (toChurch 2))

-- (m (n f)) x
-- App (App m (App n f)) x
three_times_two =
  let succ = lam (Pair (varN 0) Zero)
      times_app = App (App (varN 3) (App (varN 2) (varN 1))) (varN 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      times_type = Pair church_type (Pair church_type church_type)
      times = lam (lam (lam (lam times_app)))
  in App (App (App (App (anno times times_type) (toChurch 3)) (toChurch 2)) succ) Zero

-- m n
-- App (App (App (m n)) f) x
three_pow_two =
  let succ = lam (Pair (varN 0) Zero)
      pow_app = App (App (App (varN 3) (varN 2)) (varN 1)) (varN 0)
      church_type = Pair (Pair Zero Zero) (Pair Zero Zero)
      pow_type = Pair (Pair church_type church_type) (Pair church_type church_type)
      pow = lam (lam (lam (lam pow_app)))
  in App (App (App (App (anno pow pow_type) (toChurch 2)) (toChurch 3)) succ) Zero

-- unbound type errors should be allowed for purposes of testing runtime
allowedTypeCheck :: Maybe TypeCheckError -> Bool
allowedTypeCheck Nothing = True
allowedTypeCheck (Just (UnboundType _)) = True
allowedTypeCheck _ = False

unitTest :: String -> String -> IExpr -> IO Bool
unitTest name expected iexpr = if allowedTypeCheck (typeCheck ZeroType iexpr)
  then do
    result <- (show . PrettyIExpr) <$> optimizedEval iexpr
    if result == expected
      then pure True
      else (putStrLn $ concat [name, ": expected ", expected, " result ", result]) >>
           pure False
  else putStrLn ( concat [name, " failed typecheck: ", show (typeCheck ZeroType iexpr)])
       >> pure False

{-
unitTestOptimization :: String -> IExpr -> IO Bool
unitTestOptimization name iexpr = if optimize iexpr == optimize2 iexpr
  then pure True
  else (putStrLn $ concat [name, ": optimized1 ", show $ optimize iexpr, " optimized2 "
                          , show $ optimize2 iexpr])
  >> pure False
-}

churchType = (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType))

-- check that refinements are correct after optimization
promotingChecksPreservesType_prop :: TestIExpr -> Bool
promotingChecksPreservesType_prop (TestIExpr iexpr) =
  inferType iexpr == inferType (promoteChecks iexpr)

debugPCPT :: IExpr -> IO Bool
debugPCPT iexpr = if inferType iexpr == inferType (promoteChecks iexpr)
  then pure True
  else (putStrLn $ concat ["failed ", show iexpr, " / ", show (promoteChecks iexpr)
                          , " -- ", show (inferType iexpr), " / "
                          , show (inferType (promoteChecks iexpr))]) >> pure False

unitTests_ unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main : 0 = 0" ZeroType True
  , unitTest "two" "2" two_succ
  --, unitTest "three" "3" three_succ
  ]

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _ = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _ = False

isRefinementFailure (Just (RefinementFailure _)) = True
isRefinementFailure _ = False

unitTestQC :: Testable p => String -> p -> IO Bool
unitTestQC name p = quickCheckResult p >>= \result -> case result of
  (Success _ _ _) -> pure True
  x -> (putStrLn $ concat [name, " failed: ", show x]) >> pure False

unitTests unitTest2 unitTestType = foldl (liftA2 (&&)) (pure True)
  [ unitTestType "main : {0,0} = \\x -> {x,0}" (ArrType ZeroType ZeroType) (== Nothing)
  , unitTestType "main : {0,0} = \\x -> {x,0}" ZeroType isInconsistentType
  , unitTestType "main = succ 0" ZeroType (== Nothing)
  , unitTestType "main = succ 0" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = or 0" (ArrType ZeroType ZeroType) (== Nothing)
  , unitTestType "main = or 0" ZeroType isInconsistentType
  {- broken tests... need to fix type checking
  , unitTestType "main : {0,0} = 0" ZeroType False
  , unitTestType "main : {0,{0,0}} = \\x -> {x,0}" (ArrType ZeroType ZeroType) False
  , unitTestType "main : {0,0} = \\f -> f 0 0" (ArrType ZeroType (ArrType ZeroType ZeroType))
    False
  , unitTestType "main : 0 = \\x -> {x,0}" (ArrType ZeroType ZeroType) False
-}
  , unitTestType "main = or succ" (ArrType ZeroType ZeroType) isInconsistentType
  , unitTestType "main = 0 succ" ZeroType isInconsistentType
  , unitTestType "main = 0 0" ZeroType isInconsistentType
  , unitTestType "main : {{0,0},0} = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
    (ArrType (ArrType ZeroType ZeroType) ZeroType) isRecursiveType
  , unitTestType "main : 0 = (\\f -> f 0) (\\g -> {g,0})" ZeroType (== Nothing)
  , unitTestType "main : {{{0,0},{0,0}},{{{0,0},{0,0}},{{0,0},{0,0}}}} = \\m n f x -> m f (n f x)" (ArrType churchType (ArrType churchType churchType)) (== Nothing)
  , unitTestType "main = \\m n f x -> m f (n f x)" (ArrType churchType (ArrType churchType churchType)) (== Nothing)
  , unitTestType "main # (\\x -> if x then \"fail\" else 0) = 0" ZeroType (== Nothing)
  , unitTestType "main # (\\x -> if x then \"fail\" else 0) = 1" ZeroType isRefinementFailure
  , unitTest "three" "3" three_succ
  , unitTest "church 3+2" "5" three_plus_two
  , unitTest "3*2" "6" three_times_two
  , unitTest "3^2" "9" three_pow_two
  , unitTest "data 3+5" "8" $ App (App d_plus (i2g 3)) (i2g 5)
  , unitTest "foldr" "13" $ App (App (App foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
  , unitTest "listlength0" "0" $ App list_length Zero
  , unitTest "listlength3" "3" $ App list_length (ints2g [1,2,3])
  , unitTest "zipwith" "{{4,1},{{5,1},{{6,2},0}}}"
    $ App (App (App zipWith_ (lam (lam (Pair (varN 1) (varN 0)))))
           (ints2g [4,5,6]))
    (ints2g [1,1,2,3])
  , unitTest "listequal1" "1" $ App (App list_equality (s2g "hey")) (s2g "hey")
  , unitTest "listequal0" "0" $ App (App list_equality (s2g "hey")) (s2g "he")
  , unitTest "listequal00" "0" $ App (App list_equality (s2g "hey")) (s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
  , unitTest "map" "{2,{3,5}}" $ App (App map_ (lam (Pair (varN 0) Zero)))
    (ints2g [1,2,3])
  , unitTest2 "main = 0" "0"
  , unitTest2 fiveApp "5"
  , unitTest2 "main = plus $3 $2 succ 0" "5"
  , unitTest2 "main = times $3 $2 succ 0" "6"
  , unitTest2 "main = pow $3 $2 succ 0" "8"
  , unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
  , unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
  , unitTest2 "main = dEqual 0 0" "1"
  , unitTest2 "main = dEqual 1 0" "0"
  , unitTest2 "main = dEqual 0 1" "0"
  , unitTest2 "main = dEqual 1 1" "1"
  , unitTest2 "main = dEqual 2 1" "0"
  , unitTest2 "main = dEqual 1 2" "0"
  , unitTest2 "main = dEqual 2 2" "1"
  , unitTest2 "main = listLength []" "0"
  , unitTest2 "main = listLength [1,2,3]" "3"
  , unitTest2 "main = listEqual \"hey\" \"hey\"" "1"
  , unitTest2 "main = listEqual \"hey\" \"he\"" "0"
  , unitTest2 "main = listEqual \"hey\" \"hel\"" "0"
  , unitTest2 "main = listPlus [1,2] [3,4]" "{1,{2,{3,5}}}"
  , unitTest2 "main = listPlus 0 [1]" "2"
  , unitTest2 "main = listPlus [1] 0" "2"
  , unitTest2 "main = concat [\"a\",\"b\",\"c\"]" "{97,{98,100}}"
  , unitTest2 nestedNamedFunctionsIssue "2"
  , unitTest2 "main = take $0 [1,2,3]" "0"
  , unitTest2 "main = take $1 [1,2,3]" "2"
  , unitTest2 "main = take $5 [1,2,3]" "{1,{2,4}}"
  , unitTest2 "main = c2d (minus $4 $3)" "1"
  , unitTest2 "main = c2d (minus $4 $4)" "0"
  , unitTest2 "main = dMinus 4 3" "1"
  , unitTest2 "main = dMinus 4 4" "0"
  , unitTest2 "main = map c2d (range $2 $5)" "{2,{3,5}}"
  , unitTest2 "main = map c2d (range $6 $6)" "0"
  , unitTest2 "main = c2d (factorial $4)" "24"
  , unitTest2 "main = c2d (factorial $0)" "1"
  , unitTest2 "main = map c2d (filter (\\x -> c2d (minus x $3)) (range $1 $8))"
    "{4,{5,{6,8}}}"
  , unitTest2 "main = map c2d (quicksort [$4,$3,$7,$1,$2,$4,$6,$9,$8,$5,$7])"
    "{1,{2,{3,{4,{4,{5,{6,{7,{7,{8,10}}}}}}}}}}"
  {-
  , debugPCPT $ Gate (Check Zero Var)
  , debugPCPT $ App Var (Check Zero Var)
  , unitTestQC "promotingChecksPreservesType" promotingChecksPreservesType_prop
  , unitTestOptimization "listequal0" $ App (App list_equality (s2g "hey")) (s2g "he")
  , unitTestOptimization "map" $ App (App map_ (lam (Pair (varN 0) Zero))) (ints2g [1,2,3])
  -}
  ]

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in {a,1}\n"
  ]

fiveApp = concat
  [ "main = let fiveApp : {{0,0},{0,0}} = $5\n"
  , "       in fiveApp (\\x -> {x,0}) 0"
  ]

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest : {0,0} = \\tlb -> let f1 : {{0,0},0} = \\f -> f tlb\n"
  , "                                           f2 : {{0,0},0} = \\f -> succ (f1 f)\n"
  , "                                       in f2 succ\n"
  , "       in bindTest 0"
  ]

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    unitTestP s g = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right pg -> if pg == g
        then pure ()
        else putStrLn $ concat ["parsed oddly ", s, " ", show pg, " compared to ", show g]
    unitTest2 s r = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> fmap (show . PrettyIExpr) (optimizedEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
    unitTestType s t tef = case parseMain prelude s of
      Left e -> (putStrLn $ concat ["failed to parse ", s, " ", show e]) >> pure False
      Right g -> let apt = typeCheck t g
                 in if tef apt
                    then pure True
                    else (putStrLn $
                          concat [s, " failed typecheck, result ", show apt])
             >> pure False
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g
  result <- unitTests unitTest2 unitTestType
  exitWith $ if result then ExitSuccess else ExitFailure 1
