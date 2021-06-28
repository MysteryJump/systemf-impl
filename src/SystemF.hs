module SystemF (Type (..), FExpr (..)) where

import qualified Data.Map.Strict as Map
import qualified Untyped

data Type
  = FunType Type Type
  | TyVar String
  | Forall String Type
  | Bool
  | Nat
  deriving (Eq)

instance Show Type where
  show (FunType ty1 ty2) = "(" ++ show ty1 ++ " -> " ++ show ty2 ++ ")"
  show (TyVar ty) = ty
  show (Forall name ty) = "(forall " ++ name ++ "." ++ show ty ++ ")"
  show Bool = "bool"
  show Nat = "nat"

data FExpr ty
  = FVar String
  | FLambda String ty (FExpr ty)
  | FApply (FExpr ty) (FExpr ty)
  | FTyAbst String (FExpr ty)
  | FTyApply (FExpr ty) ty
  | FTrue
  | FFalse
  | FZero
  | FIf (FExpr ty) (FExpr ty) (FExpr ty)
  | FSucc (FExpr ty)
  | FPred (FExpr ty)
  | FIsZero (FExpr ty)
  deriving (Show)

type DepthMap = Map.Map String Integer

type TypeMap = Map.Map String Type

type TypeKeyMap = Map.Map String Integer

{- Auxiliary function -}

renameExprTy :: FExpr Type -> FExpr Type
renameExprTy = renameExprTy' Map.empty

renameExprTy' :: TypeKeyMap -> FExpr Type -> FExpr Type
renameExprTy' map (FVar str) = FVar str
renameExprTy' map (FLambda name ty expr) = FLambda name (renameType map ty) (renameExprTy' map expr)
  where
    renameType :: TypeKeyMap -> Type -> Type
    renameType m (Forall s ty) = case map Map.!? s of
      Just n -> Forall (s ++ show (n + 1)) (renameType (Map.insert name (n + 1) map) ty)
      Nothing -> Forall (s ++ "0") (renameType (Map.insert name 0 map) ty)
    renameType m (TyVar v) = TyVar (v ++ show (map Map.! v))
    renameType m (FunType t1 t2) = FunType (renameType m t1) (renameType m t2)
    renameType m Bool = Bool
    renameType m Nat = Nat
renameExprTy' map (FApply t1 t2) = FApply (renameExprTy' map t1) (renameExprTy' map t2)
renameExprTy' map (FTyAbst name expr) = case map Map.!? name of
  Just n -> FTyAbst (name ++ show (n + 1)) (renameExprTy' (Map.insert name (n + 1) map) expr)
  Nothing -> FTyAbst (name ++ "0") (renameExprTy' (Map.insert name 0 map) expr)
renameExprTy' map (FTyApply expr ty) = FTyApply (renameExprTy' map expr) ty
renameExprTy' map (FSucc expr) = FSucc (renameExprTy' map expr)
renameExprTy' map (FPred expr) = FPred (renameExprTy' map expr)
renameExprTy' map (FIsZero expr) = FIsZero (renameExprTy' map expr)
renameExprTy' map (FIf cond thn els) = FIf (renameExprTy' map cond) (renameExprTy' map thn) (renameExprTy' map els)
renameExprTy' _ ty = ty

{- Type erasure -}

tyErase :: FExpr ty -> Untyped.Expr
tyErase (FVar v) = Untyped.Var v
tyErase (FLambda name _ expr) = Untyped.Lambda name (tyErase expr)
tyErase (FApply e1 e2) = Untyped.Apply (tyErase e1) (tyErase e2)
tyErase (FTyAbst _ e) = tyErase e
tyErase (FTyApply e _) = tyErase e
tyErase FTrue = Untyped.TRUE
tyErase FFalse = Untyped.FALSE
tyErase FZero = Untyped.Zero
tyErase (FSucc n) = Untyped.Succ (tyErase n)
tyErase (FPred n) = Untyped.Pred (tyErase n)
tyErase (FIsZero n) = Untyped.IsZero (tyErase n)
tyErase (FIf cond thn els) = Untyped.If (tyErase cond) (tyErase thn) (tyErase els)

{- Type checking -}

tyCk :: FExpr Type -> Maybe Type
tyCk = tyCk' Map.empty

tyCk' :: TypeMap -> FExpr Type -> Maybe Type
tyCk' map (FVar v) = map Map.!? v
tyCk' map (FLambda name ty expr) = do
  ret <- tyCk' (Map.insert name ty map) expr
  return (FunType ty ret)
tyCk' map (FApply e1 e2) = do
  ty1 <- tyCk' map e1
  ty2 <- tyCk' map e2
  case ty1 of
    FunType f1 f2 | f1 == ty2 -> Just f2
    _ -> Nothing
tyCk' map (FTyAbst tyVar expr) = do
  ty <- tyCk' (Map.insert tyVar (TyVar tyVar) map) expr
  return (Forall tyVar ty)
tyCk' map (FTyApply expr ty) = do
  xt <- tyCk' map expr
  (varName, innerTy) <- case xt of
    Forall name ty -> Just (name, ty)
    _ -> Nothing
  return (tySubst (varName, ty) innerTy)
  where
    tySubst :: (String, Type) -> Type -> Type
    tySubst (tgtName, ty) (TyVar name) | name == tgtName = ty
    tySubst (tgtName, _) v@(TyVar name) | name /= tgtName = v
    tySubst tp (FunType t1 t2) = FunType (tySubst tp t1) (tySubst tp t2)
    tySubst (tgtName, _) (Forall name t) | name == tgtName = Forall name t
    tySubst (tgtName, ty) (Forall name t) | name /= tgtName && name `notElem` free t = Forall name (tySubst (tgtName, ty) t)
    tySubst _ _ = undefined

    free :: Type -> [String]
    free (TyVar x) = [x]
    free (Forall x ty) = [y | y <- free ty, y /= x]
    free (FunType t1 t2) = free t1 `union` free t2
    free Bool = []
    free Nat = []

    union xs ys = xs ++ [x | x <- ys, x `notElem` xs]
tyCk' _ FTrue = Just Bool
tyCk' _ FFalse = Just Bool
tyCk' _ FZero = Just Nat
tyCk' map (FSucc e) = natTyCk map e
tyCk' map (FPred e) = natTyCk map e
tyCk' map (FIsZero e) = natTyCk map e
tyCk' map (FIf cond thn els) = do
  c <- tyCk' map cond
  t <- tyCk' map thn
  e <- tyCk' map els
  case c of
    Bool | t == e -> Just t
    _ -> Nothing

natTyCk :: TypeMap -> FExpr Type -> Maybe Type
natTyCk map e = do
  ty <- tyCk' map e
  case ty of
    Nat -> Just Nat
    _ -> Nothing

{- Testing? -}

-- |
-- >>> renameExprTy renameExample -- ΛA. ((ΛA. λx: A.x) true)
-- FTyAbst "A0" (FTyAbst "A1" (FApply (FLambda "x" A1 (FVar "x")) FTrue))
-- >>> tyCk $ renameExprTy renameExample -- require type application
-- Nothing
renameExample :: FExpr Type
renameExample = FTyAbst "A" (FTyAbst "A" (FApply (FLambda "x" (TyVar "A") (FVar "x")) FTrue))

-- |
-- >>> tyCk $ renameExprTy SystemF.id
-- Just (forall X0.(X0 -> X0))
id :: FExpr Type
id = FTyAbst "X" (FLambda "x" (TyVar "X") (FVar "x")) -- ΛX. λx:X. x

-- |
-- >>> tyCk $ renameExprTy appliedId
-- Just (bool -> bool)
appliedId :: FExpr Type
appliedId = FTyApply SystemF.id Bool

-- |
-- >>> tyCk $ renameExprTy twice
-- Just (forall X0.((X0 -> X0) -> (X0 -> X0)))
twice :: FExpr Type
twice = FTyAbst "X" (FLambda "f" (FunType (TyVar "X") (TyVar "X")) (FLambda "x" (TyVar "X") (FApply (FVar "f") (FApply (FVar "f") (FVar "x")))))

-- |
-- >>> tyCk $ renameExprTy appliedTwice
-- Just ((nat -> nat) -> (nat -> nat))
appliedTwice :: FExpr Type
appliedTwice = FTyApply twice Nat

-- |
-- >>> tyCk $ renameExprTy appliedTwice2
-- Just (nat -> nat)

-- >> Untyped.runBeta 0 $ Untyped.exprToExpr' $ tyErase (FApply appliedTwice2 (FSucc (FSucc (FVar "x"))))
appliedTwice2 :: FExpr Type
appliedTwice2 = FApply appliedTwice (FLambda "x" Nat (FSucc (FSucc (FVar "x"))))

-- >> Untyped.runBeta 0 $ Untyped.exprToExpr' $ tyErase appliedTwice3
appliedTwice3 :: FExpr Type
appliedTwice3 = FApply appliedTwice2 (FSucc (FSucc (FSucc FZero)))

intToExpr' :: Untyped.Expr -> Integer -> Untyped.Expr
intToExpr' s 0 = s
intToExpr' s x = intToExpr' (Untyped.Succ s) (x - 1)

-- >>> intToExpr 12
intToExpr :: Integer -> Untyped.Expr
intToExpr = intToExpr' Untyped.Zero
