
-- modelling (non-recursive) ADTs and pretty-printing + parsing them

module Generic.ADT 

import Data.String
import Data.Vect

import Data.Nat
import Data.Fin

import Lib.Parsec
import Lib.Misc

%hide Data.Fin.Equality.FZ
%hide Data.Fin.Equality.FS

--------------------------------------------------------------------------------
-- our universe, which consists of non-recursive ADTs and tuples

mutual

  public export
  data BaseTy
    = IntB
    | BoolB
    | StringB

  public export
  data Ty : Type where
    Base : BaseTy -> Ty                          -- base types
    SumT : {n : Nat} -> Vect n Con   -> Ty       -- sum type (constructors can have several args)
    RecT : {n : Nat} -> Vect n Field -> Ty       -- record type
    TupT : {n : Nat} -> Vect n Ty    -> Ty       -- tuple type

  public export
  record Con where
    constructor MkCon
    name  : String
    nargs : Nat
    args  : Vect nargs Ty

  public export
  record Field where
    constructor MkField
    name : String
    type : Ty

--------------------------------------------------------------------------------
-- Show implementation for Ty

mutual

  Show BaseTy where
    show IntB    = "Int"
    show BoolB   = "Bool"
    show StringB = "String"
  
  Show Field where
    show (MkField name ty) = name ++ " : " ++ show ty

  Show Con where
    show (MkCon name n args) = case n of
      Z => name
      _ => name ++ " " ++ intercalate " " (map show $ toList args)
  
  Show Ty where
    show ty = case ty of
      Base base => show base
      TupT tys  => "( " ++ intercalate " , " (map show $ toList tys ) ++ " )"
      RecT flds => "{ " ++ intercalate " , " (map show $ toList flds) ++ " )"
      SumT cons => "[ " ++ intercalate " | " (map show $ toList cons) ++ " ]"

--------------------------------------------------------------------------------

export
mkSumT : List Con -> Ty
mkSumT cons = SumT (fromList cons)

export
mkRecT : List Field -> Ty
mkRecT flds = RecT (fromList flds)

export
mkTupT : List Ty -> Ty
mkTupT tys = TupT (fromList tys)

public export
IntT : Ty
IntT = Base IntB

public export
BoolT : Ty
BoolT = Base BoolB

public export
StringT : Ty
StringT = Base StringB

--------------------------------------------------------------------------------

sigTypes : Vect n Field -> Vect n Ty
sigTypes = map (\f => f.type)

sigLemma : (fvec : Vect n Field) -> (i : Fin n) 
        -> (index i (sigTypes fvec)) = ((index i fvec) .type)
sigLemma fvec i = case i of
  FZ   => case fvec of (this::_) => Refl
  FS k => case fvec of (_::rest) => sigLemma rest k -- ?rhs

--------------------------------------------------------------------------------
-- reflecting back to Idris types

mutual

  public export
  mkPiType : {n : Nat} -> Vect n Ty -> Type
  mkPiType tyVec = (i : Fin n) -> reflectTy (index i tyVec)

  public export
  mkSigType : {n : Nat} -> Vect n Ty -> Type
  mkSigType tyVec = (j : Fin n ** reflectTy (index j tyVec))

  public export
  reflectCon : Con -> Type
  reflectCon con = mkPiType con.args

  public export
  reflectBaseTy : BaseTy -> Type
  reflectBaseTy base = case base of
    IntB    => Int
    BoolB   => Bool
    StringB => String

  public export
  reflectTy : Ty -> Type
  reflectTy ty = case ty of
    Base base     => reflectBaseTy base
    SumT {n} cons => (j : Fin n ** reflectCon (index j cons))
    RecT {n} sig  => mkPiType (sigTypes sig) 
    TupT {n} tys  => mkPiType tys

-- a datatype together with a value
public export
data Data : Type where
  MkData : (ty : Ty) -> reflectTy ty -> Data

export
typeOf : Data -> Ty
typeOf (MkData ty _) = ty

--------------------------------------------------------------------------------    

sigLemma2 : (fvec : Vect n Field) -> (i : Fin n) 
        -> reflectTy (index i (sigTypes fvec)) = reflectTy ((index i fvec) .type)
sigLemma2 fvec i = cong reflectTy (sigLemma fvec i)

transport : (0 prf : a = b) -> a -> b
transport Refl x = x

--------------------------------------------------------------------------------    
-- generic pretty-printing 

export
printer : (ty : Ty) -> reflectTy ty -> String
printer = go 0 where

  Prec : Type
  Prec = Int

  app_prec : Prec
  app_prec = 10

  inParens : Bool -> String -> String
  inParens True  s = "(" ++ s ++ ")"
  inParens False s = s

  mutual

    go : Prec -> (ty : Ty) -> reflectTy ty -> String
    go d ty what = case ty of
  
      Base base => case base of
        IntB      => show what
        BoolB     => show what
        StringB   => show what
  
      SumT cons => inParens (d > app_prec) $ case what of
        (j ** ys) => goCon (index j cons) ys

      RecT sig  => "{" ++ intercalate "," (goRec sig what) ++ "}"

      TupT tys  => "(" ++ intercalate "," (goPi 0 tys what) ++ ")"

    goCon : (con : Con) -> reflectCon con -> String 
    goCon con what = case con.nargs of
      Z => con.name
      _ => con.name ++ " " ++ intercalate " " (goPi (app_prec+1) con.args what)

    goField : (fld : Field) -> reflectTy fld.type -> String
    goField (MkField name ty) what = name ++ "=" ++ go 0 ty what 

    goPi : {n : Nat} -> Prec -> (tys : Vect n Ty) -> mkPiType tys -> List String
    goPi d tvec what = map worker (enumerateFin n) where
      worker : Fin n -> String
      worker i = go d (index i tvec) (what i) 

    goRec : {n : Nat} -> (sig : Vect n Field) -> mkPiType (sigTypes sig) -> List String
    goRec fvec what = map worker (enumerateFin n) where
      worker : Fin n -> String
      worker i = 
        let prf = (sigLemma2 fvec i)
        in  goField (index i fvec) (transport prf $ what i)

export 
pretty : Data -> String
pretty (MkData ty val) = printer ty val

--------------------------------------------------------------------------------
-- generic parsing

-- dependent vector of parses (cf. mkPiType)
depLexVec : {n : Nat}  -> Vect n Ty -> Type
depLexVec {n} tyVec = (i : Fin n) -> Lexer (reflectTy (index i tyVec))

-- runs a dependent vector of parsers in order 
runDepLexVec : (n : Nat) -> (tys : Vect n Ty) -> depLexVec tys -> Lexer (mkPiType tys)
runDepLexVec n tyVec lexVec = depSequence (Parser Char) {n} Ty reflectTy tyVec lexVec 

findConIdx : String -> Vect n Con -> Maybe (Fin n)
findConIdx name Nil          = Nothing
findConIdx name (this::rest) = if name == this.name then Just FZ else map FS (findConIdx name rest)

----------------------------------------

export
parser : (ty : Ty) -> Lexer (reflectTy ty)
parser ty = mainP <|> inParens (parser ty) where

  inParens : Lazy (Lexer a) -> Lexer a
  inParens p = preWhite $ do
    _ <- postWhite $ char '('
    x <- postWhite $ p 
    _ <- postWhite $ char ')'
    pure x

  -- returns a dependent vector of parsers, which should be executed in order
  parsePiList : {n : Nat} -> Maybe Char -> Maybe Char -> (tys : Vect n Ty) -> depLexVec tys
  parsePiList {n} mbOpen sep tys = case tys of
    Nil     => \i => absurd i
    (t::ts) => \i => case i of
      FS k    => parsePiList sep sep ts k            -- not that nice hack with the two seps...
      FZ      => case mbOpen of
        Nothing    => parser t
        Just open_ => postWhite (char open_) *> parser t

  parsePi : (n : Nat) -> Char -> Char -> (tys : Vect n Ty) -> Lexer (mkPiType tys)
  parsePi n open_ sep tyVec = runDepLexVec n tyVec (parsePiList (Just open_) (Just sep) tyVec)

  parseCon : (con : Con) -> Lexer (reflectCon con)
  parseCon con = runDepLexVec con.nargs con.args (parsePiList Nothing Nothing con.args)

  parseField : (f : Field) -> Lexer (reflectTy f.type)
  parseField (MkField name ty) = do
    w <- postWhite identifier
    if w /= name then pFail else do
      _ <- postWhite (char '=')
      parser ty

  -- note: we don't allow reordering of fields, as that would complicate things a lot...
  parseFieldList : {n : Nat} -> Char -> Char -> (flds : Vect n Field) -> depLexVec (sigTypes flds)
  parseFieldList {n} open_ sep tys = case tys of
    Nil     => \i => absurd i
    (f::fs) => \i => case i of
      FZ      => postWhite (char open_) *> parseField f
      FS k    => parseFieldList sep sep fs k    

  parseRec : (n : Nat) -> (flds : Vect n Field) -> Lexer (mkPiType (sigTypes flds))
  parseRec n fldVec = runDepLexVec n (sigTypes fldVec) (parseFieldList '{' ',' fldVec)

  mainP : Lexer (reflectTy ty)
  mainP = postWhite $ preWhite $ case ty of

    Base base => case base of
      IntB      => postWhite intP
      BoolB     => postWhite boolP
      StringB   => postWhite stringLit

    TupT {n} tys  => do
      res <- parsePi n '(' ',' tys
      _   <- char ')'
      pure res
      
    SumT {n} cons => do
      word <- postWhite identifier
      case findConIdx word cons of
        Nothing => pFail
        Just j  => do
          val <- parseCon (index j cons)
          pure (j ** val)

    RecT {n} sig => do
      res <- parseRec n sig
      _   <- char '}'
      pure res

parse : (ty : Ty) -> String -> Either String Data
parse ty input = case runLexer (parser ty) input of
  Left  err => Left err
  Right val => Right (MkData ty val)

export 
unsafeParse : (ty : Ty) -> String -> Data
unsafeParse ty input = do
  case parse ty input of
    Left  err => believe_me err
    Right val => val

--------------------------------------------------------------------------------
-- parse ADT definitions 

{- the syntax is

- base types: Int, Bool, String
- tuples:     ( T1 , T2 , T3 )
- sum types:  [ Con1 A1 A2 | Con2 | Con3 C1 ]
- records:    { fld1 : T1 , fld2 : T2 , fld3 : T3 }

-}

tyParser : Lexer Ty
tyParser = preWhite tyP where

  inParens : Lazy (Lexer a) -> Lexer a
  inParens p = preWhite $ do
    _ <- postWhite $ char '('
    x <- postWhite $ p 
    _ <- postWhite $ char ')'
    pure x

  mutual
  
    tyP : Lexer Ty
    tyP = tyP_ <|> inParens tyP_ 

    tyP_ : Lexer Ty
    tyP_ = (   map Base   baseTyP 
           <|> map mkTupT tupTyP 
           <|> map mkSumT sumTyP 
           <|> map mkRecT recTyP )
  
    fieldP : Lexer Field
    fieldP = do
      name <- postWhite identifier
      _    <- postWhite (char ':')
      ty   <- postWhite tyP
      pure (MkField name ty)
  
    conP : Lexer Con
    conP = do
      con  <- postWhite identifier
      args <- many (postWhite tyP)
      pure $ MkCon con (length args) (fromList args)

    baseTyP : Lexer BaseTy
    baseTyP = do
      x <- postWhite identifier
      case x of
        "Int"    => pure IntB
        "Bool"   => pure BoolB
        "String" => pure StringB
        _        => pFail
  
    tupTyP : Lexer (List Ty)
    tupTyP = postWhite $ openCloseSepBy
      (postWhite $ char '(')
      (postWhite $ char ')')
      (postWhite $ char ',')
      (tyP)
  
    recTyP : Lexer (List Field)
    recTyP = postWhite $ openCloseSepBy
      (postWhite $ char '{')
      (postWhite $ char '}')
      (postWhite $ char ',')
      (fieldP)
  
    sumTyP : Lexer (List Con)
    sumTyP = postWhite $ openCloseSepBy
      (postWhite $ char '[')
      (postWhite $ char ']')
      (postWhite $ char '|')
      (conP)

parseTy : String -> Either String Ty
parseTy = runLexer tyParser

unsafeParseTy : String -> Ty
unsafeParseTy input = case parseTy input of
  Right ty => ty
  Left err => believe_me err

--------------------------------------------------------------------------------
-- testing

Show Data where
  show adt = pretty adt ++ " : " ++ show (typeOf adt)

export
roundtrip : Ty -> String -> IO ()
roundtrip ty input = do
  case parse ty input of
    Left  err => putStrLn err
    Right adt => putStrLn (pretty adt)

--------------------------------------------------------------------------------

tyDesc1 : String
tyDesc1 = "[ C1 Int | C2 { foo : String, bar : Bool } | C3 Bool Int | C4 (Int,Bool, Int ) ]"

ty1 : Ty
ty1 = unsafeParseTy tyDesc1

main : IO ()
main = do
  printLn $ unsafeParse ty1 "(C1  666 ) "  
  printLn $ unsafeParse ty1 " C2 { foo = (\"alma\")  ,bar= True } "  
  printLn $ unsafeParse ty1 "( C3 ((True)) (111) ) "  
  printLn $ unsafeParse ty1 " C4 ((5)  , False,77)"  

--------------------------------------------------------------------------------
