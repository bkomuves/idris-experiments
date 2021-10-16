
-- Simply Typed Lambda Calculus (extended with sum and product types and natural numbers)

module Lambda.STLC

import Data.Vect
import Decidable.Equality

import Lib.Parsec
import Lib.Misc

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
    SumT  ts  => mkSigType ts 
    ProdT ts  => mkPiType  ts
    -- VoidT     => Void
    -- UnitT     => Unit

  mkPiType : {n : Nat} -> Vect n Ty -> Type
  mkPiType tyVec = (i : Fin n) -> reflectTy (index i tyVec)

  mkSigType : {n : Nat} -> Vect n Ty -> Type
  mkSigType tyVec = (j : Fin n ** reflectTy (index j tyVec))

--------------------------------------------------------------------------------
-- equality for types (why the hell do i need to write these manually ?!?)

Eq BaseTy where
  (==) NatB     NatB      = True
  (==) IntegerB IntegerB  = True    
  (==) BoolB    BoolB     = True 
  (==) StringB  StringB   = True
  (==) _        _         = False   

Eq Ty where
  (==) (BaseT b1        ) (BaseT b2          )  = b1 == b2   
  (==) (FunT  s1 t1     ) (FunT  s2 t2       )  = s1 == s2 && t1 == t2   
  (==) (SumT  {n=n1} ts1) (SumT  {n=n2} ts2  )  = case decEq n1 n2 of { Yes Refl => ts1 == ts2 ; No _ => False }   
  (==) (ProdT {n=n1} ts1) (ProdT {n=n2} ts2  )  = case decEq n1 n2 of { Yes Refl => ts1 == ts2 ; No _ => False }
  (==) _                  _                     = False   

DecEq BaseTy where
  decEq NatB     NatB      = Yes Refl
  decEq IntegerB IntegerB  = Yes Refl    
  decEq BoolB    BoolB     = Yes Refl 
  decEq StringB  StringB   = Yes Refl
  decEq _        _         = No believe_me 

DecEq Ty where
  decEq (BaseT b1        ) (BaseT b2          )  = case decEq b1 b2 of { Yes Refl => Yes Refl ; No _ => No believe_me }
  decEq (FunT  s1 t1     ) (FunT  s2 t2       )  = case decEq s1 s2 of { Yes Refl => case decEq t1  t2  of { Yes Refl => Yes Refl ; No _ => No believe_me } ; No _ => No believe_me }
  decEq (SumT  {n=n1} ts1) (SumT  {n=n2} ts2  )  = case decEq n1 n2 of { Yes Refl => case decEq ts1 ts2 of { Yes Refl => Yes Refl ; No _ => No believe_me } ; No _ => No believe_me }   
  decEq (ProdT {n=n1} ts1) (ProdT {n=n2} ts2  )  = case decEq n1 n2 of { Yes Refl => case decEq ts1 ts2 of { Yes Refl => Yes Refl ; No _ => No believe_me } ; No _ => No believe_me }
  decEq _                  _                     = No believe_me 

--------------------------------------------------------------------------------

showBaseTy : BaseTy -> String
showBaseTy b = case b of
  NatB     => "Nat"
  IntegerB => "Int"    
  BoolB    => "Bool" 
  StringB  => "String"   

showTy : Ty -> String
showTy = go 0 where

  arr, app : Int
  arr = 5
  app = 10

  parens : Bool -> String -> String
  parens True  s = "(" ++ s ++ ")"
  parens False s = s

  go : Int -> Ty -> String
  go p ty = case ty of
    BaseT b   => showBaseTy b
    FunT  s t => parens (p > arr) $ go (arr+1) s ++ " -> " ++ go arr s
    SumT  tys => "[ " ++ intercalate " | " (map (go 0) $ toList tys) ++ " ]"
    ProdT tys => "( " ++ intercalate " , " (map (go 0) $ toList tys) ++ " )"

quotedTy : Ty -> String
quotedTy t = "`" ++ showTy t ++ "`"

Show Ty where show = showTy

--------------------------------------------------------------------------------

public export
VoidT : Ty
VoidT = SumT []

public export
UnitT : Ty
UnitT = ProdT []

tt : STLC.reflectTy UnitT
tt = \i => absurd i    -- it's represented as a dependent function `Fin 0 -> ...`

Uninhabited a => Uninhabited (DPair a f) where
  uninhabited pair = uninhabited pair.fst

public export
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

public export
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

public export
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
  Case : {k : Nat} -> {ts : Vect k Ty} -> {out : Ty} 
      -> Term ctx (SumT ts)                                      -- scrutinee
      -> ((i : Fin k) -> Term ctx (FunT (index i ts) out))       -- branches
      -> Term ctx out

--------------------------------------------------------------------------------

transportTermCtx : (ctx1 = ctx2) -> Term ctx1 ty -> Term ctx2 ty
transportTermCtx Refl tm = tm -- prf = tranport (cong2 Term prf Refl)

transportTermTy : (ty1 = ty2) -> Term ctx ty1 -> Term ctx ty2
transportTermTy Refl tm = tm -- prf = tranport (cong2 Term Refl prf)

--------------------------------------------------------------------------------

natRec : a -> (a -> a) -> Nat -> a
natRec x f n = go n x where
  go : Nat -> a -> a
  go  Z    x = x
  go (S m) x = go m (f x)

--------------------------------------------------------------------------------
-- well-typed interpreter

export
eval : {ctx : Ctx n} -> Env ctx -> Term ctx ty -> reflectTy ty
eval env term = case term of

  Kst lit  => reflectLit lit

  Var idx  => lkpEnv env idx

  Lam body => \x => eval (consEnv x env) body

  App f x  => (eval env f) (eval env x)

  Let u v  => eval (consEnv (eval env u) env) v 

  Tt       => tt

  Zero     => Z
  Succ t   => S (eval env t)

  NatElim z s n => natRec (eval env z) (eval env s) (eval env n)

  Tup us   => \i => eval env (us i)

  Inj j u  => (j ** eval env u)

  Proj j t => (eval env t) j

  Case scrutinee brs => case eval env scrutinee of
    (j ** val) => (eval env $ brs j) val

--------------------------------------------------------------------------------
-- raw (untyped) syntax 

public export
Name : Type
Name = String

public export
data Expr 
  = RKst (b : BaseTy ** Literal b)
  | RVar Name
  | RLam Name Ty Expr    -- lambda binders are annotated so that the typechecking is easy
  | RApp Expr Expr
  | RLet Name Expr Expr
  | RTt
  | RZero
  | RSucc Expr
  | RNatElim Expr Expr Expr
  | RTup (List Expr)
  | RInj Ty Nat Expr     -- target type of an injection must be annotated, because we can't infer it
  | RProj Nat Expr
  | RCase Expr (List Expr)

--------------------------------------------------------------------------------

public export
TcMsg : Type
TcMsg = String

public export
ListEnv : Type
ListEnv = List (Pair Name Ty)

record TcEnv (n : Nat) where
  constructor MkTcEnv
  names : Vect n Name
  types : Vect n Ty

consTcEnv : Name -> Ty -> TcEnv n -> TcEnv (S n)
consTcEnv name ty (MkTcEnv names tys) = MkTcEnv (name::names) (ty::tys)

consLemma1 : (name : Name) -> (ty : Ty) -> (names : Vect n Name) -> (tys : Vect n Ty) 
          -> (consTcEnv name ty (MkTcEnv names tys)).types = (ty::tys)
consLemma1 _ _ _ _ = Refl

-- we need this lemma to implement Lam and Let below
consLemma2 : (name : Name) -> (ty : Ty) -> (env : TcEnv n) -> (consTcEnv name ty env).types = (ty :: env.types)
consLemma2 name ty (MkTcEnv names tys) = consLemma1 name ty names tys

tcEnvFromListEnv : (list : ListEnv) -> TcEnv (length list)
tcEnvFromListEnv list = let vec = fromList list in MkTcEnv (map fst vec) (map snd vec) 
 
public export
record TcResult {n : Nat} (ctx : Ctx n) where
  constructor MkTcResult
  type : Ty
  term : Term ctx type

lemmaFZ : (x : a) -> (xs : Vect n a) -> x = index FZ (x :: xs)
lemmaFZ _ _ = Refl

lemmaFS : (x : a) -> (xs : Vect n a) -> (j : Fin n) -> index j xs = index (FS j) (x :: xs)
lemmaFS _ _ _ = Refl

-- this one is used for example when handling Tup
unzipTcResults : Vect k (TcResult ctx) -> (tys : Vect k Ty ** ((i : Fin k) -> Term ctx (index i tys)))
unzipTcResults vec = case vec of
  Nil => (Nil ** \i => absurd i)     -- NB. you have to eta-expand here!
  MkTcResult ty tm :: rest => case unzipTcResults rest of 
    (vec1 ** fun1) => 
      ((ty :: vec1) ** \i => case i of
        FZ   => transportTermTy (lemmaFZ ty vec1)    tm
        FS j => transportTermTy (lemmaFS ty vec1 j) (fun1 j))

-- type-checking monad
public export
TcM : Type -> Type
TcM a = Either TcMsg a

checkTyEq : (ty1 : Ty) -> (ty2 : Ty) -> TcMsg -> TcM (ty1 = ty2)
checkTyEq ty1 ty2 errmsg = case decEq ty1 ty2 of
  Yes p => Right p
  No  _ => Left  errmsg

checkBranches 
  :  {k : Nat}
  -> (sum : Vect k Ty)                           -- types of the constructors of the scrutinee sum types
  -> (brs : Vect k Ty)                           -- types of the branches (should be function types)
  -> ((i : Fin k) -> Term ctx (index i brs))     -- implementation of the branches  
  -> Maybe (out : Ty ** ((i : Fin k) -> Term ctx (FunT (index i sum) out)))  

checkBranches Nil Nil _ = Nothing     -- cannot infer output type
checkBranches (ty1::tys) (br1::brs) rhs = 
  case br1 of
    FunT _ out => case worker out (ty1::tys) (br1::brs) rhs of
      Nothing    => Nothing
      Just tms   => Just (out ** tms)
    _          => Nothing

  where

    worker
      :  {k : Nat} 
      -> (out : Ty)
      -> (sum : Vect k Ty)
      -> (brs : Vect k Ty)
      -> ((i : Fin k) -> Term ctx (index i brs))   
      -> Maybe ((i : Fin k) -> Term ctx (FunT (index i sum) out))  
    worker out Nil        _          _   = Just (\i => absurd i)
    worker out (ty1::tys) (br1::brs) rhs = case br1 of
      FunT inp out1 => case decEq inp ty1 of
        No  _    => Nothing
        Yes Refl => case decEq out out1 of
          No  _    => Nothing
          Yes Refl => case worker out tys brs (\j => rhs (FS j)) of
            Nothing  => Nothing
            Just fun => Just $ \j => case j of
              FZ   => rhs 0 
              FS k => fun k
      _ => Nothing

typeCheckEnv : {n : Nat} -> (env : TcEnv n) -> Expr -> TcM (TcResult env.types)
typeCheckEnv = go where

  go : {n : Nat} -> (env : TcEnv n) -> Expr -> TcM (TcResult env.types)
  go env expr = worker expr where

    ok : (ty : Ty) -> Term env.types ty -> TcM  (TcResult env.types)
    ok ty term = Right (MkTcResult ty term)

    bad : Msg -> TcM (TcResult env.types)
    bad = Left

    worker : Expr -> TcM (TcResult env.types)
    worker expr = case expr of
  
      RKst (b ** lit) => ok (BaseT b) (Kst lit)
  
      RVar name => case findIndex (==name) env.names of
        Nothing   => bad ("variable `" ++ name ++ "` not found in scope")
        Just i    => ok  (index i env.types) (Var i)

      -- \(x : ty1) => (body : ty2)
      RLam name ty1 body => do
        MkTcResult ty2 tm <- go (consTcEnv name ty1 env) body 
        let tbody = transportTermCtx (consLemma2 name ty1 env) tm
        ok (FunT ty1 ty2) (Lam {s=ty1} tbody)

      RApp e1 e2 => do
        MkTcResult ty1 tm1 <- go env e1
        case ty1 of
          FunT a b => do
            MkTcResult ty2 tm2 <- go env e2
            Refl <- checkTyEq a ty2 ("incompatible application: expecting " ++ quotedTy a ++ " but seeing `" ++ quotedTy ty2) 
            ok b (App tm1 tm2) -- ok  t (App tc1.term tc2.term)
          _ => bad ("application to a non-function type: " ++ quotedTy ty1)

      RLet name e1 e2 => do
        MkTcResult ty1 tm1 <- go env e1
        MkTcResult ty2 tm2 <- go (consTcEnv name ty1 env) e2
        let tm2'= transportTermCtx (consLemma2 name ty1 env) tm2
        ok ty2 (Let {s=ty1} tm1 tm2')

      RTt     => ok UnitT Tt

      RZero   => ok NatT Zero

      RSucc e => do
        MkTcResult ty tm <- go env e 
        Refl <- checkTyEq ty NatT ("applying Succ to a non-Nat type: " ++ quotedTy ty)
        ok NatT (Succ tm)

      RNatElim z s n => do
        MkTcResult tyz tmz <- go env z
        MkTcResult tys tms <- go env s
        MkTcResult tyn tmn <- go env n
        Refl <- checkTyEq tyn NatT ("applying NatElim to a non-Nat type: " ++ quotedTy tyn)
        Refl <- checkTyEq tys (FunT tyz tyz) ("incompatible arguments to NatElim")
        ok tyz (NatElim tmz tms tmn)

      RTup es => do
        results <- mapM (go env) (fromList es)
        case unzipTcResults results of
          (tys ** tms) => ok (ProdT tys) (Tup tms)

      RProj k e => do
        MkTcResult ty tm <- go env e
        case ty of
          ProdT {n=m} tys => case natToFin k m of
            Just j  => ok (index j tys) (Proj j tm)
            Nothing => bad ("projection index out of range")
          _ => bad ("projection applied to a non-product type: " ++ quotedTy ty)

      RInj tgt k e => case tgt of
        SumT {n=m} tys => case natToFin k m of
          Just j => do
            MkTcResult ty tm <- go env e
            Refl <- checkTyEq ty (index j tys) ("injection type mismatch; expected: " ++ quotedTy (index j tys) ++ " vs. inferred: " ++ quotedTy ty)
            ok (SumT tys) (Inj j tm)
          Nothing => bad ("injection index out of range")
        _ => bad ("target type of an injection must be a sum type")

      RCase scrutinee branches => do
        MkTcResult ty tm <- go env scrutinee
        case ty of
          SumT {n=m} tys => do
            bresults <- mapM (go env) (fromList branches)
            case unzipTcResults bresults of
              (rtys ** rhss) => case decEq m (length branches) of
                No  _    => bad ("number of branches in case expression does not match the number of constructors of the scrutinee")
                Yes Refl => case checkBranches tys rtys rhss of
                  Just (out ** tbranches) => ok out (Case tm tbranches)
                  Nothing => bad ("type mismatch in case branches vs. the scrutinee constructors")
          _ => bad ("scrutinee of case is not a sum type")

--------------------------------------------------------------------------------

typeCheck : (env : ListEnv) -> Expr -> Either TcMsg (TcResult (tcEnvFromListEnv env).types)
typeCheck env expr = typeCheckEnv (tcEnvFromListEnv env) expr

--------------------------------------------------------------------------------
