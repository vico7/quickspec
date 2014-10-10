{-# LANGUAGE CPP #-}
module QuickSpec.Pruning where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Equation
import Control.Monad.Trans.State.Strict

class Pruner a where
  emptyPruner :: a
  unifyUntyped :: PruningTerm -> PruningTerm -> State a Bool
  repUntyped :: PruningTerm -> State a (Maybe PruningTerm)

unify :: Pruner a => Equation -> State a Bool
unify e = unifyUntyped (encodeTypes (lhs e)) (encodeTypes (rhs e))

rep :: Pruner a => Term -> State a (Maybe Term)
rep t = fmap (fmap decodeTypes) (repUntyped (encodeTypes t))

type PruningTerm = Tm PruningConstant PruningVariable

data PruningConstant
  = TermConstant Constant
  | TypeConstant TyCon
  | HasType
  deriving (Eq, Ord, Show)

instance Pretty PruningConstant where
  pretty (TermConstant x) = pretty x
  pretty (TypeConstant x) = pretty x
  pretty HasType = text "@"

data PruningVariable
  = TermVariable Variable
  | TypeVariable TyVar
  deriving (Eq, Ord, Show)

instance Pretty PruningVariable where
  pretty (TermVariable x) = pretty x
  pretty (TypeVariable x) = pretty x

encodeTypes :: Term -> PruningTerm
encodeTypes t = tag t (inner t)
  where
    tag t u =
      Fun HasType [mapTerm TypeConstant TypeVariable (typ t), u]
    inner (Var x) = Var (TermVariable x)
    inner (Fun f xs) = Fun (TermConstant f) (map encodeTypes xs)

decodeTypes :: PruningTerm -> Term
decodeTypes (Fun HasType [_, Var (TermVariable x)]) = Var x
decodeTypes (Fun HasType [_, Fun (TermConstant f) xs]) =
  Fun f (map decodeTypes xs)