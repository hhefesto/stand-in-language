{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Common
import           Control.Monad
import qualified Control.Monad.State       as State
import           Data.Algorithm.Diff       (getGroupedDiff)
import           Data.Algorithm.DiffOutput (ppDiff)
import           Data.Bifunctor
import           Data.Either               (fromRight)
import           Data.Functor.Foldable
import           Data.Map                  (Map, fromList, toList)
import qualified Data.Map                  as Map
import qualified Data.Semigroup            as Semigroup
import qualified Data.Set                  as Set
import           Debug.Trace               (trace)
import           SIL
import           SIL.Eval
import           SIL.Parser
import           SIL.RunTime
import qualified System.IO.Strict          as Strict
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.HUnit
import           Text.Megaparsec
import           Text.Megaparsec.Debug
import           Text.Megaparsec.Error

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res `compare` True @?= EQ
  ,testCase "test ITE 1" $ do
      res <- parseSuccessful parseITE testITE1
      res `compare` True @?= EQ
  , testCase "test ITE 2" $ do
      res <- parseSuccessful parseITE testITE2
      res `compare` True @?= EQ
  , testCase "test ITE 3" $ do
      res <- parseSuccessful parseITE testITE3
      res `compare` True @?= EQ
  , testCase "test ITE 4" $ do
      res <- parseSuccessful parseITE testITE4
      res `compare` True @?= EQ
  , testCase "test ITE with Pair" $ do
      res <- parseSuccessful parseITE testITEwPair
      res `compare` True @?= EQ
  , testCase "test if Complete Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testCompleteLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test if Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testLambdawITEwPair
      res `compare` True @?= EQ
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseAssignmentwCLwITEwPair1
      res `compare` True @?= EQ
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseTopLevelwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "test parseMain with CL with ITE with Pair parses" $ do
      res <- runTestMainwCLwITEwPair
      res `compare` True @?= EQ
  , testCase "testList0" $ do
      res <- parseSuccessful parseList testList0
      res `compare` True @?= EQ
  , testCase "testList1" $ do
      res <- parseSuccessful parseList testList1
      res `compare` True @?= EQ
  , testCase "testList2" $ do
      res <- parseSuccessful parseList testList2
      res `compare` True @?= EQ
  , testCase "testList3" $ do
      res <- parseSuccessful parseList testList3
      res `compare` True @?= EQ
  , testCase "testList4" $ do
      res <- parseSuccessful parseList testList4
      res `compare` True @?= EQ
  , testCase "testList5" $ do
      res <- parseSuccessful parseList testList5
      res `compare` True @?= EQ
  , testCase "test parse Prelude.sil" $ do
      res <- runTestParsePrelude
      res `compare` True @?= EQ
  , testCase "test parse tictactoe.sil" $ do
      res <- testWtictactoe
      res `compare` True @?= EQ
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res `compare` True @?= EQ
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard0
      res `compare` True @?= EQ
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard1
      res `compare` True @?= EQ
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard2
      res `compare` True @?= EQ
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard3
      res `compare` True @?= EQ
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard4
      res `compare` True @?= EQ
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard5
      res `compare` True @?= EQ
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful (parseApplied) testShowBoard6
      res `compare` True @?= EQ
  , testCase "testLetShowBoard0" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard0
      res `compare` True @?= EQ
  , testCase "testLetShowBoard1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard1
      res `compare` True @?= EQ
  , testCase "testLetShowBoard2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard2
      res `compare` True @?= EQ
  , testCase "testLetShowBoard3" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard3
      res `compare` True @?= EQ
  , testCase "testLetShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testLetShowBoard4
      res `compare` True @?= EQ
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
      res `compare` True @?= EQ
  , testCase "testLetShowBoard8" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard8
      res `compare` True @?= EQ
  , testCase "testLetShowBoard9" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard9
      res `compare` True @?= EQ
  , testCase "AST terms as functions" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app left (pair zero zero)"
      res `compare` True @?= EQ
  , testCase "left with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "left (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "right with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "right (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res `compare` True @?= EQ
  , testCase "trace with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "trace (\\x -> (\\y -> (x,y))) 0 0"
      res `compare` True @?= EQ
  , testCase "app with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app (\\x y z -> x) 0 1 2"
      res `compare` True @?= EQ
  , testCase "testLetIndentation" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIndentation
      res `compare` True @?= EQ
  , testCase "testLetIncorrectIndentation1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation1
      res `compare` False @?= EQ
  , testCase "testLetIncorrectIndentation2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation2
      res `compare` False @?= EQ
  -- , testCase "collect vars" $ do
  --     let fv = vars expr
  --     fv `compare` (Set.empty) @?= EQ
  -- , testCase "collect vars many x's" $ do
  --     let fv = vars expr1
  --     fv `compare` (Set.empty) @?= EQ
  , testCase "test automatic open close lambda" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> \\y -> (x, y)"
      (fromRight TZero $ validateVariables [] res) `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 2" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x y -> (x, y)"
      (fromRight TZero $ validateVariables [] res) `compare` closedLambdaPair @?= EQ
  , testCase "test automatic open close lambda 3" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> z"
      (fromRight TZero $ validateVariables [] res) `compare` expr6 @?= EQ
  , testCase "test automatic open close lambda 4" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> (x, x)"
      (fromRight TZero $ validateVariables [] res) `compare` expr5 @?= EQ
  , testCase "test automatic open close lambda 5" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> \\x -> \\x -> x"
      (fromRight TZero $ validateVariables [] res) `compare` expr4 @?= EQ
  , testCase "test automatic open close lambda 6" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> [x,y,z]"
      (fromRight TZero $ validateVariables [] res) `compare` expr3 @?= EQ
  , testCase "test automatic open close lambda 7" $ do
      res <- runSILParser (parseLambda <* scn <* eof) "\\a -> (a, (\\a -> (a,0)))"
      (fromRight TZero $ validateVariables [] res) `compare` expr2 @?= EQ
  ]

-- myTrace a = trace (show a) a

dependantTopLevelBindings = unlines $
  [ "f = (1,0)"
  , "g = (0,1)"
  , "main = [f,g,f]"
  ]

myDebug = do
  preludeFile <- Strict.readFile "Prelude.sil"
  case parseWithPrelude [] dependantTopLevelBindings of
    Right r -> putStrLn . show . optimizeBindingsReference $ r
    Left l  -> putStrLn l

-- |\y z -> [zz, yy0, yy0, z, zz]
expr10 = LetUP [("zz", IntUP 8)] $
           LamUP "y" (LamUP "z" (ListUP [PairUP (VarUP "zz") (IntUP 0),VarUP "yy0",VarUP "yy0",VarUP "z",VarUP "zz"]))

-- flattenOuterLetUP (LetUP l (LetUP l' x)) = LetUP (l' <> l) x
-- flattenOuterLetUP x = x

myDebug2 = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let prelude = case parsePrelude preludeFile of
                  Right p -> p
                  Left pe -> error . getErrorString $ pe
  let (upt, new, old) = rename prelude' expr10
      prelude' = (extractBindings expr10) <> prelude
      -- expr10' = applyUntilNoChange flattenOuterLetUP $ prelude' expr10
  putStrLn $ show upt <> "\nnew: " <> show new <> "\nold: " <> show old

-- myDebug2 = do
--   let (t1, _, _) = rename (ParserState (Map.insert "zz" TZero $ Map.insert "yy0" TZero initialMap ))
--                               expr8
--   putStrLn . show $ x Map.! "h"

-- |Usefull to see if tictactoe.sil was correctly parsed
-- and was usefull to compare with the deprecated SIL.Parser
-- Parsec implementation
testWtictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "hello.sil"
  let
    prelude = case parsePrelude preludeFile of
                Right p -> p
                Left pe -> error . getErrorString $ pe
  case parseMain prelude tictactoe of
    Right _ -> return True
    Left _  -> return False

{-
runTictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "hello.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  runSILParser_ parseTopLevel tictactoe
-}
  -- case parseWithPrelude prelude tictactoe of
  --   Right x -> putStrLn . show $ x
  --   Left err -> putStrLn . getErrorString $ err

-- parseWithPreludeFile = do
--   preludeFile <- Strict.readFile "Prelude.sil"
--   file <- Strict.readFile "hello.sil"
--   let
--     prelude = case parsePrelude preludeFile of
--                 Right p -> p
--                 Left pe -> error . getErrorString $ pe
--     printBindings :: Map String Term1 -> IO ()
--     printBindings xs = forM_ (toList xs) $
--                        \b -> do
--                          putStr "  "
--                          putStr . show . fst $ b
--                          putStr " = "
--                          putStrLn $ show . snd $ b
--   case parseWithPrelude prelude file of
--     Right r -> printBindings r
--     Left l -> putStrLn . show $ l


  -- let (t1, _, _) = rename (ParserState (Map.insert "zz" TZero $ Map.insert "yy0" TZero initialMap ) Map.empty)
  --                         topLevelBindingNames
  --                         expr8
  -- putStrLn . show $ t1
  -- putStrLn . show $ (expr9 :: Term1)

  -- case parseWithPrelude prelude' dependantTopLevelBindings of
  --   Right x -> do
  --     -- expected :: Term1 <- runSILParser (parseApplied <* scn <* eof) "(\\f0 g1 f1 x -> (x, [f0, g1, x, f1])) f g f"
  --     putStrLn . show $ (x Map.! "h") -- `compare` expected @?= EQ
  --   Left err -> error . show $ err

letExpr = unlines $
  [ "let x = 0"
  , "    y = 0"
  , "    f = (x,y)"
  , "in f"
  ]

-- | SIL Parser AST representation of: \x -> \y -> \z -> [zz1, yy3, yy4, z, zz6]
expr9 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("zz1"))
                (TPair
                  (TVar ("yy3"))
                  (TPair
                    (TVar ("yy5"))
                    (TPair
                      (TVar ("z"))
                      (TPair
                        (TVar ("zz6"))
                        TZero)))))))

-- | SIL Parser AST representation of: \x -> \y -> \z -> [zz, yy0, yy0, z, zz]
expr8 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("zz"))
                (TPair
                  (TVar ("yy0"))
                  (TPair
                    (TVar ("yy0"))
                    (TPair
                      (TVar ("z"))
                      (TPair
                        (TVar ("zz"))
                        TZero)))))))

-- | SIL Parser AST representation of: "\z -> [x,x,y,x,z,y,z]"
expr7 = TLam (Open ("z"))
          (TPair
            (TVar ("x"))
            (TPair
              (TVar ("x"))
              (TPair
                (TVar ("y"))
                (TPair
                  (TVar ("x"))
                  (TPair
                    (TVar ("z"))
                    (TPair
                      (TVar ("y"))
                      (TPair
                        (TVar ("z"))
                        TZero)))))))

-- | SIL Parser AST representation of: \x -> \y -> \z -> z
expr6 :: Term1
expr6 = TLam (Closed ("x"))
          (TLam (Closed ("y"))
            (TLam (Closed ("z"))
              (TVar ("z"))))

-- | SIL Parser AST representation of: \x -> (x, x)
expr5 = TLam (Closed ("x"))
          (TPair
            (TVar ("x"))
            (TVar ("x")))

-- | SIL Parser AST representation of: \x -> \x -> \x -> x
expr4 = TLam (Closed ("x"))
          (TLam (Closed ("x"))
            (TLam (Closed ("x"))
              (TVar ("x"))))

-- | SIL Parser AST representation of: \x -> \y -> \z -> [x,y,z]
expr3 = TLam (Closed ("x"))
          (TLam (Open ("y"))
            (TLam (Open ("z"))
              (TPair
                (TVar ("x"))
                (TPair
                  (TVar ("y"))
                  (TPair
                    (TVar ("z"))
                    TZero)))))

-- | SIL Parser AST representation of: \a -> (a, (\a -> (a,0)))
expr2 = TLam (Closed ("a"))
          (TPair
            (TVar ("a"))
            (TLam (Closed ("a"))
              (TPair
                (TVar ("a"))
                TZero)))


-- | SIL Parser AST representation of: \x -> [x, x, x]
expr1 = TLam (Closed ("x"))
          (TPair
            (TVar ("x"))
            (TPair
              (TVar ("x"))
              (TPair
                (TVar ("x"))
                TZero)))

expr = TLam (Closed ("x"))
         (TLam (Open ("y"))
           (TPair
             (TVar ("x"))
             (TVar ("y"))))

range = unlines
  [ "range = \\a b -> let layer = \\recur i -> if dMinus b i"
  , "                                           then (i, recur (i,0))"
  , "                                           else 0"
  , "                in ? layer (\\i -> 0) a"
  , "r = range 2 5"
  ]

closedLambdaPair = TLam (Closed ("x")) (TLam (Open ("y")) (TPair (TVar ("x")) (TVar ("y"))))

testLetIndentation = unlines
  [ "let x = 0"
  , "    y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation1 = unlines
  [ "let x = 0"
  , "  y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation2 = unlines
  [ "let x = 0"
  , "      y = 1"
  , "in (x,y)"
  ]

testPair0 = "(\"Hello World!\", \"0\")"

testPair1 = unlines
  [ "("
  , " \"Hello World!\""
  , ", \"0\""
  , ")"
  ]

testITE1 = unlines $
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 = unlines $
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 = unlines $
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 = unlines $
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair = unlines $
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair = unlines $
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.sil"
  case parsePrelude preludeFile of
    Right _ -> return True
    Left _  -> return False

testParseAssignmentwCLwITEwPair2 = unlines $
  [ "main = \\input -> if 1"
  , "                  then"
  , "                   (\"Hello, world!\", 0)"
  , "                  else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair3 = unlines $
  [ "main = \\input ->"
  , "  if 1"
  , "   then"
  , "     (\"Hello, world!\", 0)"
  , "   else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair4 = unlines $
  [ "main = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair5 = unlines $
  [ "main"
  , "  = \\input"
  , "-> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair6 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "    then"
  , "       (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair7 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "       then"
  , "             (\"Hello, world!\", 0)"
  , "           else (\"Goodbye, world!\", 0)"
  ]
testParseAssignmentwCLwITEwPair1 = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair = unlines $
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMain3 = "main = 0"

test4 = "(\\x -> if x then \"f\" else 0)"
test5 = "\\x -> if x then \"f\" else 0"
test6 = "if x then \"1\" else 0"
test7 = unlines $
  [ "if x then \"1\""
  , "else 0"
  ]
test8 = "if x then 1 else 0"

runTestMainwCLwITEwPair = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude testMainwCLwITEwPair of
    Right x  -> return True
    Left err -> return False

testMain2 = "main : (\\x -> if x then \"fail\" else 0) = 0"

runTestMainWType = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude $ testMain2 of
    Right x  -> return True
    Left err -> return False

testList0 = unlines $
  [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 = "[0,1,2]"

testList2 = "[ 0 , 1 , 2 ]"

testList3 = unlines $
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 = unlines $
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 = unlines $
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

-- -- |Helper function to debug tictactoe.sil
-- debugTictactoe :: IO ()
-- debugTictactoe  = do
--   preludeFile <- Strict.readFile "Prelude.sil"
--   tictactoe <- Strict.readFile "tictactoe.sil"
--   let prelude =
--         case parsePrelude preludeFile of
--           Right pf -> pf
--           Left pe -> error . getErrorString $ pe
--       p str = State.runStateT $ parseMain prelude str
--   case runParser (dbg "debug" p) "" tictactoe of
--     Right (a, s) -> do
--       putStrLn ("Result:      " ++ show a)
--       putStrLn ("Final state: " ++ show s)
--     Left err -> putStr (errorBundlePretty err)

runTictactoe = do
  preludeFile <- Strict.readFile "Prelude.sil"
  tictactoe <- Strict.readFile "tictactoe.sil"
  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error . getErrorString $ pe
  case parseMain prelude $ tictactoe of
    Right x  -> pure ()
    Left err -> putStrLn err


-- -- |Parse main.
-- parseMain' :: Bindings -> String -> Either ErrorString Term1
-- parseMain' prelude s = parseWithPrelude prelude s >>= getMain where
--   getMain bound = case Map.lookup "main" bound of
--     Nothing -> fail "no main method found"
--     Just main -> pure main--splitExpr <$> debruijinize [] main

testITEParsecResult = "TITE (TPair TZero TZero) (TPair TZero TZero) (TPair (TPair TZero TZero) TZero)"

-- TODO: does it matter that one parses succesfuly and the other doesnt?
parseApplied0 = unlines
  [ "foo (bar baz"
  , "     )"
  ]
parseApplied1 = unlines
  [ "foo (bar baz"
  , "      )"
  ]


testShowBoard0 = unlines
  [ "main = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)))"
  , "          (1)"
  ]

testShowBoard1 = unlines
  [ "main = or (0)"
  , "               (1)"
  ]

testShowBoard2 = unlines
  [ "main = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 = unlines
  [ "main = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testLetShowBoard0 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        (and (not winner)"
  , "                             (not filledBoard)"
  , "                        )"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard1 = unlines
  [ "let showBoard = or (0)"
  , "                   (1)"
  , "in 0"
  ]

testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard4 = unlines
  [ "main = or (and 0"
  , "                    1)"
  , "               (not boardIn)"
  ]

testLetShowBoard8 = unlines
  [ "or (0"
  , "   )"
  , "   1"
  ]
testLetShowBoard9 = unlines
  [ "or 0"
  , "   1"
  ]

testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
  ]

testShowBoard4 = unlines
  [ "main = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 = unlines
  [ "main = or (or x"
  , "                   (or 0"
  , "                       1))"
  , "               (1)"
  ]

fiveApp = concat
  [ "main = let fiveApp = $5\n"
  , "       in fiveApp (\\x -> (x,0)) 0"
  ]

showAllTransformations :: String -- ^ SIL code
                       -> IO ()
showAllTransformations input = do
  preludeFile <- Strict.readFile "Prelude.sil"
  let section description body = do
        putStrLn "\n-----------------------------------------------------------------"
        putStrLn $ "----" <> description <> ":\n"
        putStrLn $ body
      prelude = case parsePrelude preludeFile of
                  Right x  -> x
                  Left err -> error . getErrorString $ err
      upt = case parseWithPrelude prelude input of
              Right x -> x
              Left x  -> error x
  section "Input" input
  section "UnprocessedParsedTerm" $ show upt
  section "optimizeBuiltinFunctions" $ show . optimizeBuiltinFunctions $ upt
  let optimizeBuiltinFunctionsVar = optimizeBuiltinFunctions upt
      str1 = lines . show $ optimizeBuiltinFunctionsVar
      str0 = lines . show $ upt
      diff = getGroupedDiff str0 str1
  section "Diff optimizeBuiltinFunctions" $ ppDiff diff
  let optimizeBindingsReferenceVar = optimizeBindingsReference optimizeBuiltinFunctionsVar
      str2 = lines . show $ optimizeBindingsReferenceVar
      diff = getGroupedDiff str1 str2
  section "optimizeBindingsReference" . show $ optimizeBindingsReferenceVar
  section "Diff optimizeBindingsReference" $ ppDiff diff
  let validateVariablesVar = validateVariables prelude optimizeBindingsReferenceVar
      str3 = lines . show $ validateVariablesVar
      diff = getGroupedDiff str3 str2
  section "validateVariables" . show $ validateVariablesVar
  section "Diff validateVariables" $ ppDiff diff
  let Right debruijinizeVar = (>>= debruijinize []) validateVariablesVar
      str4 = lines . show $ debruijinizeVar
      diff = getGroupedDiff str4 str3
  section "debruijinize" . show $ debruijinizeVar
  section "Diff debruijinize" $ ppDiff diff
  let splitExprVar = splitExpr debruijinizeVar
      str5 = lines . show $ splitExprVar
      diff = getGroupedDiff str5 str4
  section "splitExpr" . show $ splitExprVar
  section "Diff splitExpr" $ ppDiff diff
  let Just toSILVar = toSIL . findChurchSize $ splitExprVar
      str6 = lines . show $ toSILVar
      diff = getGroupedDiff str6 str5
  section "toSIL" . show $ toSILVar
  section "Diff toSIL" $ ppDiff diff
  -- let evalLoopVar = evalLoop toSILVar
  --     str0 = lines . show $ toSILVar
  --     diff = getGroupedDiff str0 str1
  -- section "toSIL" . show $ evalLoopVar
  -- section "Diff toSIL" $ ppDiff diff
