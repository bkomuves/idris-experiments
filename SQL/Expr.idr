
-- Expression mini-language

module SQL.Expr

import Decidable.Equality
import SQL.Sig

--------------------------------------------------------------------------------
-- well-typed expression language

public export
data CmpOp   = Lt | Gt | Le | Ge

public export
data BoolOp1 = Not

public export
data BoolOp2 = And | Or | Xor

public export
data NumOp1  = Negate

public export
data NumOp2  = Add | Sub | Times

public export
data StrOp1  = Reverse

public export
data StrOp2  = Append

mutual 

  -- well-typed expressions
  public export
  data Expr : Sig -> Ty -> Type where
    EVar     : {ctx : Sig} -> {name : Name} -> (prf : FieldOf name ctx) -> Expr ctx (lookupTy prf)
    EKst     : (ty : Ty) -> reflectTy ty -> Expr ctx ty
    ERecord  : ExprRec ctx sig -> Expr ctx (RecT sig)
    EEqualOp : TyEq  ty ->            Expr ctx ty      -> Expr ctx ty      -> Expr ctx BoolT
    ECmpOp   : TyOrd ty -> CmpOp   -> Expr ctx ty      -> Expr ctx ty      -> Expr ctx BoolT
    EBoolOp1 :             BoolOp1 -> Expr ctx BoolT   -> Expr ctx BoolT  
    EBoolOp2 :             BoolOp2 -> Expr ctx BoolT   -> Expr ctx BoolT   -> Expr ctx BoolT
    ENumOp1  :             NumOp1  -> Expr ctx IntT    -> Expr ctx IntT    
    ENumOp2  :             NumOp2  -> Expr ctx IntT    -> Expr ctx IntT    -> Expr ctx IntT
    EStrOp1  :             StrOp1  -> Expr ctx StringT -> Expr ctx StringT
    EStrOp2  :             StrOp2  -> Expr ctx StringT -> Expr ctx StringT -> Expr ctx StringT
  
  -- a record of expressions in a given context. The first Sig is the context, the second the record type
  public export
  data ExprRec : Sig -> Sig -> Type where
    ExprRecNil  : ExprRec cyx Nil
    ExprRecCons : {fld : Field} -> Expr ctx (fieldTy fld) -> ExprRec ctx rest -> ExprRec ctx (fld :: rest)

--------------------------------------------------------------------------------

-- interprets an expression in a context
public export
evalExpr : {ctx : Sig} -> Rec ctx -> Expr ctx ty -> reflectTy ty
evalExpr {ctx} env expr = go expr where 

  mutual

    go : forall t. Expr ctx t -> reflectTy t
    go expr = case expr of
  
      EVar prf => extractRecordField prf env

      EKst _ x => x

      EEqualOp impl e1 e2 => (==) @{impl} (go e1) (go e2)

      ECmpOp impl op e1 e2 => case op of
        Lt  => (<)  @{impl} (go e1) (go e2)
        Gt  => (>)  @{impl} (go e1) (go e2)
        Le  => (<=) @{impl} (go e1) (go e2)
        Ge  => (>=) @{impl} (go e1) (go e2)

      EBoolOp1 op e1 => case op of
        Not => not (go e1)
    
      EBoolOp2 op e1 e2 => case op of
        And => go e1 && go e2
        Or  => go e1 || go e2
        Xor => xor (go e1) (go e2)
    
      ENumOp1 op e1 => case op of
        Negate => negate (go e1)
    
      ENumOp2 op e1 e2 => case op of
        Add   => go e1 + go e2
        Sub   => go e1 - go e2
        Times => go e1 * go e2
    
      EStrOp1 op e1 => case op of
        Reverse => reverse (go e1)
  
      EStrOp2 op e1 e2 => case op of
        Append => go e1 ++ go e2
  
      ERecord erec => goRec erec
  
    goRec : forall sig. ExprRec ctx sig -> Rec sig
    goRec  ExprRecNil        = RecNil
    goRec (ExprRecCons e es) = RecCons (go e) (goRec es)
  
    xor : Bool -> Bool -> Bool
    xor True  False = True
    xor False True  = True
    xor _     _     = False

-- same but in different argument order, returning a function
public export
runExpr : {sig : Sig} -> Expr sig ty -> (Rec sig -> reflectTy ty)
runExpr expr input = evalExpr input expr

--------------------------------------------------------------------------------
-- raw (untyped) mini-language

public export
data RawKst 
  = RawInt    Int 
  | RawBool   Bool 
  | RawString String

-- untyped expressions
public export
data RawExpr : Type where
  RVar     : Name    -> RawExpr
  RKst     : RawKst  -> RawExpr
  REqualOp :            RawExpr -> RawExpr -> RawExpr
  RCmpOp   : CmpOp   -> RawExpr -> RawExpr -> RawExpr
  RBoolOp1 : BoolOp1 -> RawExpr -> RawExpr
  RBoolOp2 : BoolOp2 -> RawExpr -> RawExpr -> RawExpr
  RNumOp1  : NumOp1  -> RawExpr -> RawExpr
  RNumOp2  : NumOp2  -> RawExpr -> RawExpr -> RawExpr
  RStrOp1  : StrOp1  -> RawExpr -> RawExpr
  RStrOp2  : StrOp2  -> RawExpr -> RawExpr -> RawExpr
--  RRecord  : List (Pair Name RawExpr) -> RawExpr

--------------------------------------------------------------------------------

-- typechecks an expression in a context
public export
typeCheckRawExpr : (ctx : Sig) -> RawExpr -> Maybe (t : Ty ** Expr ctx t)
typeCheckRawExpr ctx raw = go raw where

  go : RawExpr -> Maybe (t : Ty ** Expr ctx t)
  go raw = case raw of

    RVar name => case isFieldOf name ctx of
      Nothing   => Nothing
      Just prf  => Just (lookupTy prf ** EVar prf)

    RKst kst => case kst of
      RawInt    i => Just (IntT    ** EKst IntT    i)
      RawBool   b => Just (BoolT   ** EKst BoolT   b)
      RawString s => Just (StringT ** EKst StringT s)

    REqualOp r1 r2 => case (go r1, go r2) of
      (Just (t1 ** e1) , Just (t2 ** e2)) => case decEq t1 t2 of
        Yes Refl => case mbTyEq t1 of
          Just impl => Just (BoolT ** EEqualOp impl e1 e2)
          Nothing   => Nothing
        No  _    => Nothing
      (_ , _) => Nothing

    RCmpOp op r1 r2 => case (go r1, go r2) of
      (Just (t1 ** e1) , Just (t2 ** e2)) => case decEq t1 t2 of
        Yes Refl => case mbTyOrd t1 of
          Just impl => Just (BoolT ** ECmpOp impl op e1 e2)
          Nothing   => Nothing
        No  _    => Nothing
      (_ , _) => Nothing
 
    RBoolOp1 op r1 => case (go r1) of
      Just (BoolT ** e1) => Just (BoolT ** EBoolOp1 op e1)
      _ => Nothing

    RBoolOp2 op r1 r2 => case (go r1, go r2) of
      (Just (BoolT ** e1) , Just (BoolT ** e2)) => Just (BoolT ** EBoolOp2 op e1 e2)
      (_ , _) => Nothing

    RNumOp1 op r1 => case (go r1) of
      Just (IntT ** e1) => Just (IntT ** ENumOp1 op e1)
      _ => Nothing

    RNumOp2 op r1 r2 => case (go r1, go r2) of
      (Just (IntT ** e1) , Just (IntT ** e2)) => Just (IntT ** ENumOp2 op e1 e2)
      (_ , _) => Nothing

    RStrOp1 op r1 => case (go r1) of
      Just (StringT ** e1) => Just (StringT ** EStrOp1 op e1)
      _ => Nothing

    RStrOp2 op r1 r2 => case (go r1, go r2) of
      (Just (StringT ** e1) , Just (StringT ** e2)) => Just (StringT ** EStrOp2 op e1 e2)
      (_ , _) => Nothing

--------------------------------------------------------------------------------

{-

exSig2 : Sig
exSig2 = 
  [ MkField "foo1" IntT
  , MkField "bar1" StringT
  , MkField "baz1" BoolT
--  , MkField "rec1" (RecT [ MkField "alma" BoolT , MkField "korte" IntT ])
  , MkField "foo2" IntT
  , MkField "bar2" StringT
  , MkField "baz2" BoolT
--  , MkField "rec2" (RecT [ MkField "alma" BoolT , MkField "korte" IntT ])
  ]

exRec2 : Rec Expr.exSig2
exRec2 = RecCons 123
       $ RecCons "alma"
       $ RecCons True
       $ RecCons 246
       $ RecCons "korte"
       $ RecCons False
       $ RecNil

exRawE : RawExpr
exRawE = 
--  RStrOp2 Append (RVar "bar1") (RStrOp1 Reverse (RVar "bar2"))
  REqualOp (RNumOp2 Times (RVar "foo1") (RKst (RawInt 2))) (RVar "foo2")

test : IO Unit
test = do
  case typeCheckRawExpr exSig2 exRawE of
    Nothing => putStrLn "typecheck failed"
    Just p  => case snd p of
      expr    => printTy (evalExpr exRec2 expr)

-}

--------------------------------------------------------------------------------

