
-- Simply Typed Lambda Calculus

module Lambda.STLC

import Data.Vect

--------------------------------------------------------------------------------
-- the universe of object language types

mutual

  public export
  data BaseTy
    = NatB
    | IntegerB
    | BoolB
    | StringB

  public export
  data Ty : Type where
    BaseT  : BaseTy -> Ty
    FunT   : Ty -> Ty -> Ty
    VoidT  : Ty
    UnitT  : Ty
    SumT   : {n : Nat} -> Vect n Ty -> Ty
    ProdT  : {n : Nat} -> Vect n Ty -> Ty

  reflectBaseTy : BaseTy -> Type
  reflectBaseTy b = case b of
    NatB     => Nat
    IntegerB => Integer
    BoolB    => Bool
    StringB  => String

  public export
  reflectTy : Ty -> Type
  reflectTy ty = case ty of
    BaseT b   => reflectBaseTy b
    FunT  s t => reflectTy s -> reflectTy t
    VoidT     => Void
    UnitT     => Unit
    SumT  ts  => mkSigType ts 
    ProdT ts  => mkPiType  ts

  mkPiType : {n : Nat} -> Vect n Ty -> Type
  mkPiType tyVec = (i : Fin n) -> reflectTy (index i tyVec)

  mkSigType : {n : Nat} -> Vect n Ty -> Type
  mkSigType tyVec = (j : Fin n ** reflectTy (index j tyVec))

--------------------------------------------------------------------------------

NatT : Ty
NatT = BaseT NatB

--------------------------------------------------------------------------------
-- the context

Ctx : (n : Nat) -> Type
Ctx n = Vect n Ty

lkpCtx : {n : Nat} -> (ctx : Ctx n) -> Fin n -> Ty
lkpCtx ctx i = index i ctx

Env : {n : Nat} -> Ctx n -> Type
Env ctx = mkPiType ctx

lkpEnv : {n : Nat} -> {ctx : Ctx n} -> Env ctx -> (i : Fin n) -> reflectTy (lkpCtx ctx i)
lkpEnv env i = env i

consEnv : (x : reflectTy t) -> (xs : mkPiType ts) -> mkPiType (t::ts)
consEnv x xs = \i => case i of
  FZ   => x
  FS k => xs k

--------------------------------------------------------------------------------
-- literals

data Literal : BaseTy -> Type where
  NatLit     : Nat     -> Literal NatB
  IntegerLit : Integer -> Literal IntegerB
  BoolLit    : Bool    -> Literal BoolB
  StringLit  : String  -> Literal StringB

reflectLit : Literal b -> reflectTy (BaseT b)
reflectLit lit = case lit of
  NatLit     n => n
  IntegerLit i => i
  BoolLit    b => b
  StringLit  s => s

--------------------------------------------------------------------------------
-- well-typed syntax

data Term : Ctx n -> Ty -> Type where

  -- literal costants
  Kst : {b : BaseTy} -> Literal b -> Term ctx (BaseT b)

  -- variables (using de Bruijn indices)
  Var : {n : Nat} -> {ctx : Ctx n} -> (i : Fin n) -> Term ctx (lkpCtx ctx i)

  -- lambda abstraction
  Lam : {s : Ty} -> Term (s :: ctx) t -> Term ctx (FunT s t)

  -- application
  App : Term ctx (FunT s t) -> Term ctx s -> Term ctx t

  -- let abstraction
  Let : {s : Ty} -> Term ctx s -> Term (s :: ctx) t -> Term ctx t

  ------------------

  -- the single element (constructor) of the unit type
  Tt : Term ctx UnitT
 
  -- ex falso (eliminator of the empty type)
  ExFalso : Term cyx (FunT VoidT ty)

  -- constructors of the Nat type
  Zero : Term ctx NatT
  Succ : Term ctx NatT -> Term ctx NatT
  
  -- recursor (Nat eliminator)
  NatElim : Term ctx ty -> Term ctx (FunT ty ty) -> Term ctx NatT -> Term ctx ty

  -- tuple (constructor for product type)
  Tup : {ts : Vect k Ty} -> ((i : Fin k) -> Term ctx (index i ts)) -> Term ctx (ProdT ts)

  -- injection (constructor for sum type)
  Inj : {ts : Vect k Ty} -> (j : Fin k) -> Term ctx (index j ts) -> Term ctx (SumT ts)

  -- projection (eliminator for the product type)
  Proj : {ts : Vect k Ty} -> (j : Fin k) -> Term ctx (ProdT ts) -> Term ctx (index j ts)

  -- case analyis (eliminator for the sum type)
  Case : {ts : Vect k Ty} -> {out : Ty} 
      -> ((i : Fin k) -> Term ctx (FunT (index i ts) out)) -> Term ctx (SumT ts) -> Term ctx out

--------------------------------------------------------------------------------

natRec : a -> (a -> a) -> Nat -> a
natRec x f n = go n x where
  go : Nat -> a -> a
  go  Z    x = x
  go (S m) x = go m (f x)

--------------------------------------------------------------------------------
-- well-typed interpreter

eval : {ctx : Ctx n} -> Env ctx -> Term ctx ty -> reflectTy ty
eval env term = case term of

  Kst lit  => reflectLit lit

  Var idx  => lkpEnv env idx

  Lam body => \x => eval (consEnv x env) body

  App f x  => (eval env f) (eval env x)

  Let u v  => eval (consEnv (eval env u) env) v 

  Tt       => MkUnit

  ExFalso  => absurd

  Zero     => Z
  Succ t   => S (eval env t)

  NatElim z s n => natRec (eval env z) (eval env s) (eval env n)

  Tup us   => \i => eval env (us i)

  Inj j u  => (j ** eval env u)

  Proj j t => (eval env t) j

  Case brs scrutinee => case eval env scrutinee of
    (j ** val) => (eval env $ brs j) val

--------------------------------------------------------------------------------
