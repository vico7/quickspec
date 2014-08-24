-- | The main implementation of QuickSpec.

{-# LANGUAGE CPP, TypeOperators, TypeFamilies, TypeSynonymInstances, FlexibleInstances #-}
module Test.QuickSpec.Main where

#include "errors.h"

import Test.QuickSpec.Generate
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as EQ
import qualified Test.QuickSpec.Reasoning.Z3 as Z3
import qualified Test.QuickSpec.Reasoning.E as E
import qualified Test.QuickSpec.Reasoning.Crappy as Crappy
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Term hiding (symbols, eval)
import Control.Monad
import Text.Printf
import Data.Monoid
import Test.QuickSpec.TestTree(TestResults, classes, reps)
import Data.List
import System.Random
import Data.Monoid
import Data.Maybe
import Test.QuickSpec.Utils
import Test.QuickSpec.Equation

class Monad m => Reasoner m where
  data Context m
  initial :: Int -> [Symbol] -> [Tagged Term] -> Context m
  eval :: Context m -> m a -> a
  unify :: Equation -> m Bool

instance Reasoner EQ.EQ where
  newtype Context EQ.EQ = EQC EQ.Context
  initial d ss univ = EQC (EQ.initial d ss univ)
  eval (EQC x) = EQ.evalEQ x
  unify = EQ.unify

instance Reasoner Z3.EQ where
  newtype Context Z3.EQ = Z3C Z3.Context
  initial d ss univ = Z3C (Z3.initial d ss univ)
  eval (Z3C x) = Z3.evalEQ x
  unify = Z3.unify

instance Reasoner E.EQ where
  newtype Context E.EQ = EC E.Context
  initial d ss univ = EC (E.initial d ss univ)
  eval (EC x) = E.evalEQ x
  unify = E.unify

instance Reasoner Crappy.EQ where
  newtype Context Crappy.EQ = CC Crappy.Context
  initial d ss univ = CC (Crappy.initial d ss univ)
  eval (CC x) = Crappy.evalEQ x
  unify = Crappy.unify

undefinedsSig :: Sig -> Sig
undefinedsSig sig =
  background
    [ undefinedSig "undefined" (undefined `asTypeOf` witness x)
    | Some x <- saturatedTypes sig ]

universe :: [[Tagged Term]] -> [Tagged Term]
universe css = filter (not . isUndefined . erase) (concat css)

prune :: Reasoner m => Context m -> [Term] -> (a -> Equation) -> [a] -> [a]
prune ctx reps erase eqs = eval ctx (filterM (liftM not . unify . erase) eqs)

defines :: Equation -> Maybe Symbol
defines (t :=: u) = do
  let isVar Var{} = True
      isVar _ = False

      acyclic t =
        all acyclic (args t) &&
        case functor t == functor u of
          True -> usort (map Var (vars t)) `isProperSubsetOf` args u
          False -> True
      xs `isProperSubsetOf` ys = xs `isSubsetOf` ys && sort xs /= sort ys
      xs `isSubsetOf` ys = sort xs `isSublistOf` sort ys
      [] `isSublistOf` _ = True
      (x:xs) `isSublistOf` [] = False
      (x:xs) `isSublistOf` (y:ys)
        | x == y = xs `isSublistOf` ys
        | otherwise = (x:xs) `isSublistOf` ys

  guard (all isVar (args u) && usort (args u) == args u &&
         acyclic t && vars t `isSubsetOf` vars u)

  return (functor u)

definitions :: [Equation] -> [Equation]
definitions es = [ e | e <- es, defines e /= Nothing ]

runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = do
  putStrLn "== API =="
  putStr (show (signature sig_))
  let sig = signature sig_ `mappend` undefinedsSig (signature sig_)

  tool sig

data Target = Target Symbol | NoTarget deriving (Eq, Ord)

target :: Equation -> Target
target (t :=: u) =
  case usort (filter p (funs t ++ funs u)) of
    [f] -> Target f
    _ -> NoTarget
  where p x = not (silent x) && symbolArity x > 0

innerZip :: [a] -> [[b]] -> [[(a,b)]]
innerZip [] _ = []
innerZip _ [] = []
innerZip xs ([]:yss) = []:innerZip xs yss
innerZip (x:xs) ((y:ys):yss) =
  let (zs:zss) = innerZip xs (ys:yss)
  in ((x,y):zs):zss

isAlphaRenamed sig t = all ok (partitionBy symbolType (vars t)) || isCommy t
  where
    isCommy (Var _) = True
    isCommy (App (Const _) (Var _)) = True
    isCommy (App (App (Const _) (Var x)) (Var y)) | x /= y = True
    isCommy _ = False
    ok vs@(v:_) = ok' (map index vs) [ index v' | v' <- summaryVariables (summarise sig), symbolType v == symbolType v' ]
    ok' [] _ = True
    ok' (x:xs) (y:ys) | x == y = ok' (filter (/= x) xs) ys
    ok' _ _ = False

-- | Run QuickSpec on a signature.
quickSpec :: Signature a => a -> IO ()
quickSpec = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generateTermsSatisfying False (isAlphaRenamed sig) (const partialGen) sig
  let clss = concatMap (some2 (map (Some . O) . classes)) (TypeMap.toList r)
      univ = concatMap (some2 (map (tagged term))) clss
      reps = map (some2 (tagged term . head)) clss
      eqs = equations clss
  printf "%d raw equations; %d terms in universe.\n\n"
    (length eqs)
    (length reps)

  let ctx1 = initial (maxDepth sig) (symbols sig) univ :: Context Crappy.EQ
      ctx2 = initial (maxDepth sig) (symbols sig) univ :: Context E.EQ
      reps' = filter (not . isUndefined) (map erase reps)
      allEqs = map (some eraseEquation) eqs
      isBackground = all silent . eqnFuns
      keep eq = not (isBackground eq) || absurd eq
      absurd (t :=: u) = absurd1 t u || absurd1 u t
      absurd1 (Var x) t = x `notElem` vars t
      absurd1 _ _ = False
      (background, foreground) =
        partition isBackground allEqs
      pruned = filter keep
                 (--prune ctx2 reps' id
                   (prune ctx1 reps' id
                    (background ++ foreground)))
      eqnFuns (t :=: u) = funs t ++ funs u
      isGround (t :=: u) = null (vars t) && null (vars u)
      byTarget = innerZip [1 :: Int ..] (partitionBy target pruned)

  forM_ byTarget $ \eqs@((_,eq):_) -> do
    case target eq of
      NoTarget -> putStrLn "== Equations about several functions =="
      Target f -> printf "== Equations about %s ==\n" (show f)
    forM_ eqs $ \(i, eq) ->
      printf "%3d: %s\n" i (showEquation sig eq)
    putStrLn ""

sampleList :: StdGen -> Int -> [a] -> [a]
sampleList g n xs | n >= length xs = xs
                  | otherwise = aux g n (length xs) xs
  where
    aux g 0 _ _ = []
    aux g _ _ [] = ERROR "sampleList: bug in sampling"
    aux g size len (x:xs)
      | i <= size = x:aux g' (size-1) (len-1) xs
      | otherwise = aux g' size (len-1) xs
      where (i, g') = randomR (1, len) g

-- | Generate random terms from a signature. Useful when QuickSpec is
--   generating too many terms and you want to know what they look like.
sampleTerms :: Signature a => a -> IO ()
sampleTerms = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generate False (const partialGen) (updateDepth (maxDepth sig - 1) sig)
  let univ = sort . concatMap (some2 (map term)) . TypeMap.toList . terms sig .
             TypeMap.mapValues2 reps $ r
  printf "Universe contains %d terms.\n\n" (length univ)

  let numTerms = 100

  printf "== Here are %d terms out of a total of %d ==\n" numTerms (length univ)
  g <- newStdGen
  forM_ (zip [1 :: Int ..] (sampleList g numTerms univ)) $ \(i, t) ->
    printf "%d: %s\n" i (show (mapVars (disambiguate sig (vars t)) t))

  putStrLn ""
