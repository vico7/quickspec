{-# LANGUAGE ExistentialQuantification #-}
module Test.QuickSpec.Reasoning.Z3 where

import Test.QuickSpec.Term hiding (sym)
import Test.QuickSpec.Equation
import Control.Monad.Trans
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.Typeable
import Z3.Monad hiding (Symbol, Context, reset)
import Z3.Opts
import System.IO
import System.IO.Unsafe
import Data.List
import Control.Monad.State

data ManyZ3 a = Return a | Reset (ManyZ3 a) | forall b. Step (Z3 b) (b -> ManyZ3 a)

instance Monad ManyZ3 where
  return = Return
  Return x >>= f = f x
  Reset x >>= f = Reset (x >>= f)
  Step x k >>= f = Step x (\y -> k y >>= f)

instance MonadIO ManyZ3 where
  liftIO x = Step (liftIO x) return

step :: ManyZ3 a -> Z3 (ManyZ3 a)
step (Step x f) = x >>= step . f
step x = return x

runManyZ3 :: ManyZ3 a -> IO a
runManyZ3 (Return x) = return x
runManyZ3 (Reset x) = runManyZ3 x
runManyZ3 x = evalZ3With Nothing (opt "SOFT_TIMEOUT" (1000 :: Int)) (step x) >>= runManyZ3

reset :: ManyZ3 ()
reset = Reset (Return ())

type Context = ()
type EQ = StateT [Equation] ManyZ3

liftZ3 :: Z3 a -> EQ a
liftZ3 x = lift (Step x return)

reload :: EQ ()
reload = do
  lift reset
  eqs <- get
  liftZ3 (sequence_ [ flattenEquation eq >>= assertCnstr | eq <- eqs ])

initial :: Int -> [Symbol] -> [Tagged Term] -> Context
initial _ _ _ = ()

evalEQ :: Context -> EQ a -> a
evalEQ ctx x = unsafePerformIO (runManyZ3 (evalStateT x []))

unify :: Equation -> EQ Bool
unify eq = do
  liftIO (putStr (show eq ++ ": ") >> hFlush stdout)
  prop <- liftZ3 (flattenEquation eq)
  res <- liftZ3 (local (mkNot prop >>= assertCnstr >> check))
  liftIO (print res)
  case res of
    Unsat ->
      -- Pruned
      return True
    _ -> do
      -- Not pruned
      modify (eq:)
      reload
      return False

flattenEquation (t :=: u) = do  
  t' <- flatten t
  u' <- flatten u
  mkEq t' u' >>= quantify (nub (vars t ++ vars u))

quantify [] t = return t
quantify xs t = do
  apps <- mapM (flatten . Var) xs >>= mapM toApp
  mkForallConst [] apps t

mkSym s = mkIntSymbol (index s)
mkSort t = mkStringSymbol (show t) >>= mkUninterpretedSort

flatten :: Term -> Z3 AST
flatten t =
  let f = functor t
      as = args t in
  case as of
    [] -> do
      sym <- mkSym f
      sort <- mkSort (symbolType f)
      mkConst sym sort
    _ -> do
      sym <- mkSym f
      let (args, res) = symbolTypes f
      args' <- mapM mkSort args
      res' <- mkSort res
      func <- mkFuncDecl sym args' res'
      mapM flatten as >>= mkApp func

symbolTypes :: Symbol -> ([TypeRep], TypeRep)
symbolTypes s = loop (symbolArity s) (symbolType s)
  where
    loop 0 ty = ([], ty)
    loop n ty = (x:xs, ys)
      where
        Just (x, ty') = splitArrow ty
        (xs, ys) = loop (n-1) ty'
