-- | Equations.

module Test.QuickSpec.Equation where

import Test.QuickSpec.Term
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Utils.Typed
import Data.Monoid
import Data.List
import Data.Ord
import Data.List.Split
import Data.Char

data Equation = Term :=: Term deriving (Eq, Ord)

showEquation :: Sig -> Equation -> String
showEquation sig (t :=: u) =
  show (mapVars f t) ++ " == " ++ show (mapVars f u)
  where f = disambiguate sig (vars t ++ vars u)

stringToEquation :: String -> Sig  -> Equation
stringToEquation "" sig = error "Empty String"
stringToEquation str sig = do	
  let (leftTerm : rightTerm :empty) =(splitOn "==" (removeWhitspace str))
  (symbolsToTerms (getVarCon sig) (stringToSymbol (getSymbols sig) leftTerm)) 
  	:=: (symbolsToTerms (getVarCon sig) (stringToSymbol (getSymbols sig) 
      rightTerm))

instance Show Equation where
  show = showEquation mempty

data TypedEquation a = Expr a :==: Expr a

eraseEquation :: TypedEquation a -> Equation
eraseEquation (e1 :==: e2) = term e1 :=: term e2

instance Eq (TypedEquation a) where
  e1 == e2 = e1 `compare` e2 == EQ

instance Ord (TypedEquation a) where
  compare = comparing eraseEquation

instance Show (TypedEquation a) where
  show = show . eraseEquation

showTypedEquation :: Sig -> TypedEquation a -> String
showTypedEquation sig e = showEquation sig (eraseEquation e)

equations :: [Several Expr] -> [Some TypedEquation]
equations = sortBy (comparing (some eraseEquation)) .
            concatMap (several toEquations)
  where toEquations (x:xs) = [Some (y :==: x) | y <- xs]

removeWhitspace :: String -> String 
removeWhitspace str = filter (/= ' ') str


groupPar :: String -> [[Char]]
groupPar str = groupPar' str []

groupPar' :: String -> String -> [[Char]]
groupPar' [] list  = [list]
groupPar' (x:xs) list = if (x == '(') 
                        then ((groupPar' (snd(help xs [])) list) 
                            ++ [fst(help xs [])] )  
                        else (groupPar' xs (list++ [x]) )
  where help (y:ys) list = if (y == ')') 
                           then (list, ys ) 
                           else (help ys (list ++ [y]))


stringToSymbol :: [(String , Symbol)] -> String ->  [[Symbol]]
stringToSymbol sym str = map (stringToSymbol' sym) (groupPar str)

stringToSymbol' :: [(String , Symbol)] -> String ->  [Symbol]
stringToSymbol' sym (x:xs)  = stringToSymbol'' ([x] ,xs) sym

stringToSymbol'' :: (String, String) -> [(String , Symbol)] -> [Symbol]
stringToSymbol'' ([],[]) _ = []
stringToSymbol'' ( x ,(y:ys)) list = case (find ((x == ) . fst) list)  of
                    Just a -> (([snd a]) ++ (stringToSymbol'' ([y], ys) list))
                    Nothing ->  (stringToSymbol'' (x ++ [y], ys) list)
stringToSymbol'' ( x ,[]) list = case (find ((x == ) . fst) list)  of
                              Just a -> [snd a]
                              Nothing -> error "Undefined Symbol" 