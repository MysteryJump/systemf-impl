module Untyped (eval, Expr (..), runBeta, beta, exprToExpr') where

import Data.Char
import qualified Data.Map.Strict as Map
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim
import Text.Parsec.String

data Expr
  = Var String
  | Lambda String Expr
  | Apply Expr Expr
  | TRUE
  | FALSE
  | If Expr Expr Expr
  | Succ Expr
  | Pred Expr
  | IsZero Expr
  | Zero
  deriving (Show)

type DepthMap = Map.Map String Integer

-- de Bruijn indexed
data Expr'
  = Var' Integer
  | Lambda' Expr'
  | Apply' Expr' Expr'
  | TRUE'
  | FALSE'
  | If' Expr' Expr' Expr'
  | Succ' Expr'
  | Pred' Expr'
  | IsZero' Expr'
  | Zero'
  deriving (Eq)

withParen :: String -> String
withParen inner = "(" ++ inner ++ ")"

instance Show Expr' where
  show (Apply' expr1 expr2) = "(" ++ show expr1 ++ " " ++ show expr2 ++ ")"
  show (Lambda' expr) = "(λ. " ++ show expr ++ ")"
  show (Var' num) = show num
  show TRUE' = "true"
  show FALSE' = "false"
  show (If' cond thn els) = "if " ++ show cond ++ " then " ++ show thn ++ " else " ++ show els
  show (IsZero' expr) = "iszero" ++ withParen (show expr)
  show (Succ' expr) =
    case countSucc 0 expr of
      Just n -> "'" ++ show n
      Nothing -> "succ" ++ withParen (show expr)
  show (Pred' expr) = "pred" ++ withParen (show expr)
  show Zero' = "'0"

countSucc :: Integer -> Expr' -> Maybe Integer
countSucc x Zero' = Just x
countSucc x (Succ' n) = countSucc (x + 1) n
countSucc _ _ = Nothing

-- to de Bruijn indexed expr
toExpr' :: Expr -> (DepthMap, Integer) -> Expr'
toExpr' (Apply ex exp) s = Apply' (toExpr' ex s) (toExpr' exp s)
toExpr' (Lambda str expr) s = Lambda' (toExpr' expr (Map.insert str (snd s) (fst s), snd s + 1))
toExpr' (Var str) s = case fst s Map.!? str of
  Nothing -> Var' (-1)
  Just n -> Var' (snd s - n - 1)
toExpr' TRUE _ = TRUE'
toExpr' FALSE _ = FALSE'
toExpr' (If cond thn els) s = If' (toExpr' cond s) (toExpr' els s) (toExpr' thn s)
toExpr' (Pred p) s = Pred' (toExpr' p s)
toExpr' (Succ p) s = Succ' (toExpr' p s)
toExpr' (IsZero p) s = IsZero' (toExpr' p s)
toExpr' Zero _ = Zero'

{- Substition -}
shift ::
  Integer ->
  Integer ->
  Expr' ->
  Expr'
shift c num (Var' k) | k < c = Var' k
shift c num (Var' k) | k >= c = Var' (k + num)
shift c num (Lambda' expr) = Lambda' (shift (c + 1) num expr)
shift c num (Apply' t1 t2) = Apply' (shift c num t1) (shift c num t2)
shift c num (Succ' s) = Succ' (shift c num s)
shift c num (Pred' s) = Pred' (shift c num s)
shift c num (IsZero' s) = IsZero' (shift c num s)
shift c num (If' cond thn els) = If' (shift c num els) (shift c num thn) (shift c num els)
shift _ _ expr = expr

shift0 :: Integer -> Expr' -> Expr'
shift0 = shift 0

substitute ::
  Expr' ->
  Expr' ->
  Integer ->
  Expr'
substitute s (Var' k) j | k == j = s
substitute s (Var' k) j | k /= j = Var' k
substitute s l@(Lambda' t) j =
  Lambda' (substitute (shift0 1 s) t (j + 1))
substitute s (Apply' t1 t2) j = Apply' (substitute s t1 j) (substitute s t2 j)
substitute s (Succ' e) j = Succ' (substitute s e j)
substitute s (Pred' e) j = Pred' (substitute s e j)
substitute s (IsZero' e) j = IsZero' (substitute s e j)
substitute s (If' cond thn els) j = If' (substitute s cond j) (substitute s thn j) (substitute s els j)
substitute _ expr _ = expr

{- Evaluation -}

beta :: Expr' -> Maybe Expr'
beta (Apply' e1 e2) | not (isValue e1) =
  do
    e <- beta e1
    Just (Apply' e e2)
beta (Apply' e1 e2) | isValue e1 && not (isValue e2) =
  do
    e <- beta e2
    Just (Apply' e1 e)
beta (Apply' (Lambda' t) v)
  | isValue v =
    Just (shift0 (-1) $ substitute (shift0 1 v) t 0)
beta (If' cond thn els) = do
  c <- beta cond
  case c of
    TRUE' -> beta thn
    FALSE' -> beta els
    _ -> Nothing
beta (Succ' s) | not (isValue s) = do
  e <- beta s
  Just (Succ' e)
beta (Pred' (Succ' s)) = Just s
beta (Pred' Zero') = Just Zero'
beta (Pred' s) | not (isValue s) = do
  e <- beta s
  Just (Pred' e)
beta (IsZero' s) = do
  e <- beta s
  case e of
    Zero' -> Just TRUE'
    Succ' _ -> Just FALSE'
    _ -> Nothing
beta TRUE' = Just TRUE'
beta FALSE' = Just FALSE'
beta Zero' = Just Zero'
beta _ = Nothing

isValue :: Expr' -> Bool
isValue TRUE' = True
isValue FALSE' = True
isValue (Lambda' _) = True
isValue Zero' = True
isValue (Succ' s) = isValue s
isValue _ = False

eval :: String -> IO ()
eval = run parseExpr

{- Parser? -}

exprToExpr' :: Expr -> Expr'
exprToExpr' = flip toExpr' (Map.empty, 0)

run :: Parser Expr -> String -> IO ()
run p input =
  case parse p "hoge" input of
    Left err ->
      do
        putStr "parse error at"
        print err
    Right x ->
      print $
        runBeta 0 $
          exprToExpr' x

runBeta :: Integer -> Expr' -> Either Expr' Expr'
runBeta depth expr =
  case result of
    Just s ->
      if isValue s
        then Right s
        else runBeta (depth + 1) s
    _ -> Left expr
  where
    result = beta expr

ch :: Parser Char
ch = noneOf "().\\ "

whitespace :: Parser ()
whitespace = do
  many $ oneOf " "
  return ()

parseExpr :: Parser Expr
parseExpr = parenExpr <|> exprIdent

exprIdent :: Parser Expr
exprIdent = do
  whitespace
  str <- many ch
  whitespace
  return
    ( case str of
        "true" -> TRUE
        "false" -> FALSE
        _ -> Var str
    )

exprAbst :: Parser Expr
exprAbst = do
  oneOf "\\"
  whitespace
  ident <- many ch
  oneOf "."
  whitespace
  Lambda ident <$> parseExpr

parenExpr :: Parser Expr
parenExpr = do
  whitespace
  oneOf "("
  whitespace
  expr <- try exprAbst <|> exprApply
  whitespace
  oneOf ")"
  return expr

exprApply :: Parser Expr
exprApply = do
  expr1 <- parseExpr
  whitespace
  Apply expr1 <$> parseExpr

{- Testing? -}

test :: Expr'
test = Lambda' (Lambda' (Apply' (Var' 1) (Apply' (Var' 0) (Var' 2))))

test2 :: Expr'
test2 = Lambda' (Apply' (Apply' (Var' 0) (Var' 1)) (Lambda' (Apply' (Apply' (Var' 0) (Var' 1)) (Var' 2))))

betaTest :: Maybe Expr'
betaTest = beta $ Apply' (Lambda' (Apply' (Apply' (Var' 1) (Var' 0)) (Var' 2))) (Lambda' (Var' 0))