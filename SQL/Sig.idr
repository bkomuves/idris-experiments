
-- Types and signatures

module SQL.Sig

import Decidable.Equality

import Lib.Misc

--------------------------------------------------------------------------------

public export
Name : Type
Name = String

--------------------------------------------------------------------------------

mutual

  public export
  data Field : Type where
    MkField : Name -> Ty -> Field 
  
  -- we need to compare types for equality when parsing, so we have to 
  -- model the universe and reflect it back to Idris types...
  public export
  data Ty : Type where
    IntT    : Ty
    BoolT   : Ty
    StringT : Ty
    RecT    : Sig -> Ty
    FunT    : Ty -> Ty -> Ty

  -- reflects back the types of our universe into the host languages
  public export
  reflectTy : Ty -> Type
  reflectTy t = case t of
    IntT       => Int
    BoolT      => Bool
    StringT    => String
    RecT sig   => Rec sig
    FunT t1 t2 => (reflectTy t1 -> reflectTy t2) 

  -- a record signature
  public export
  Sig : Type
  Sig = List Field

  -- a record
  public export
  data Rec : Sig -> Type where
    RecNil  : Rec Nil
    RecCons : {fld : Field} -> reflectTy (fieldTy fld) -> Rec rest -> Rec (fld :: rest)

  public export
  fieldName : Field -> Name
  fieldName (MkField n _) = n

  public export
  fieldTy : Field -> Ty
  fieldTy (MkField _ t) = t

  public export
  fieldType : Field -> Type
  fieldType (MkField _ t) = reflectTy t

--------------------------------------------------------------------------------

public export
DataSet : Sig -> Type
DataSet sig = List (Rec sig)

--------------------------------------------------------------------------------

public export
exSig : Sig
exSig = 
  [ MkField "foo" IntT
  , MkField "bar" StringT
  , MkField "baz" BoolT
  ]

--------------------------------------------------------------------------------
-- Decidable equality for types

fieldLemma : (MkField n1 t1 = MkField n2 t2) -> (n1 = n2, t1 = t2) 
fieldLemma Refl = (Refl, Refl)

funtLemma : (FunT t1 u1 = FunT t2 u2) -> (t1 = t2, u1 = u2) 
funtLemma Refl = (Refl, Refl)

rectLemma : (RecT sig1 = RecT sig2) -> (sig1 = sig2)
rectLemma Refl = Refl

mutual
  
  public export
  DecEq Field where

    -- ** does not parse :( **
    -- decEq (MkField n1 t1) (MkField n2 t2) with (decEq n1 n2, decEq t1 t2)
    --    | (Yes Refl, Yes Refl) = Yes Refl
    --    | (No  dprf, _       ) = No (\q => dprf (fst $ fieldLemma q))
    --    | (_       , No  dprf) = No (\q => dprf (snd $ fieldLemma q))
  
    decEq (MkField n1 t1) (MkField n2 t2) = case decEq n1 n2 of
       No  dprf => No (\q => dprf (fst $ fieldLemma q))
       Yes Refl => case decEq t1 t2 of
         No  dprf => No (\q => dprf (snd $ fieldLemma q))
         Yes Refl => Yes Refl
  
  public export
  DecEq Ty where
  
    decEq IntT    IntT    = Yes Refl
    decEq BoolT   BoolT   = Yes Refl
    decEq StringT StringT = Yes Refl
  
    decEq (FunT t1 u1) (FunT t2 u2) = case decEq t1 t2 of
      No  dprf => No (\q => dprf (fst $ funtLemma q))
      Yes Refl => case decEq u1 u2 of
        No  dprf => No (\q => dprf (snd $ funtLemma q))
        Yes Refl => Yes Refl
  
    decEq (RecT sig1) (RecT sig2) = case decEq sig1 sig2 of
      Yes Refl => Yes Refl
      No  dprf => No (\q => dprf (rectLemma q))
  
    decEq _ _ = No believe_me      -- ugly hack but this should by derived by the compiler anyway?!

--------------------------------------------------------------------------------
-- Eq / Ord instances for records (I think this is not actually used anywhere?)

Eq (Rec Nil) where
  RecNil == RecNil = True

(Eq (reflectTy ty), Eq (Rec sig)) => Eq (Rec (MkField name ty :: sig)) where
  (RecCons x xs) == (RecCons y ys) = (x == y) && (xs == ys)

Ord (Rec Nil) where
  compare RecNil RecNil = EQ

(Ord (reflectTy ty), Ord (Rec sig)) => Ord (Rec (MkField name ty :: sig)) where
  compare (RecCons x xs) (RecCons y ys) = case compare x y of
    LT => LT
    GT => GT
    EQ => compare xs ys

--------------------------------------------------------------------------------
-- Show instance for our reflected universe

mutual

  public export
  showTy : {ty : Ty} -> reflectTy ty -> String
  showTy x = case ty of
    IntT     => show x
    BoolT    => show x
    StringT  => show x
    FunT _ _ => "<function>"
    RecT sig => "{ " ++ showRec x ++ " }"

  public export
  showRec : {sig : Sig} -> Rec sig -> String
  showRec RecNil = ""
  showRec (RecCons x xs) = case sig of
    Nil                    => ""
    (MkField name ty :: _) => case xs of
      RecNil      => name ++ " = " ++ showTy x 
      RecCons _ _ => name ++ " = " ++ showTy x ++ " , " ++ showRec xs
  
{ty : Ty} -> Show (reflectTy ty) where
  show = showTy

public export
printTy : {ty : Ty} -> reflectTy ty -> IO Unit
printTy = putStrLn . showTy

--------------------------------------------------------------------------------

-- proof that a name is present in a signature
public export
data FieldOf : Name -> Sig -> Type where
  FieldHead : {ty  : Ty } -> FieldOf name (MkField name ty :: sig)
  FieldTail : {sig : Sig} -> FieldOf name sig -> FieldOf name (fld :: sig)

-- constructs such a proof
public export
isFieldOf : (name : Name) -> (sig : Sig) -> Maybe (FieldOf name sig)
isFieldOf name Nil = Nothing
isFieldOf name (MkField n t :: rest) = case decEq n name of
    Yes Refl => Just FieldHead 
    No  _    => case isFieldOf name rest of
      Nothing   => Nothing
      Just prf' => Just (FieldTail prf')

-- looks up the type of a field in a signature
public export
lookupTy : FieldOf name sig -> Ty
lookupTy (FieldHead {ty}) = ty
lookupTy (FieldTail prf') = lookupTy prf'

public export
lookupType : FieldOf name sig -> Type
lookupType = reflectTy . lookupTy

-- reconstructs the field
public export
lookupField : {name : Name} -> FieldOf name sig -> Field
lookupField {name} prf = MkField name (lookupTy prf)

-- we can test it this way
public export
mbLookupTy : Name -> Sig -> Maybe Ty
mbLookupTy name sig = case isFieldOf name sig of
  Nothing  => Nothing
  Just prf => Just (lookupTy prf)

-- extracts the given field from a record
public export
extractRecordField : (prf : FieldOf name sig) -> Rec sig -> lookupType prf 
extractRecordField (FieldHead     ) (RecCons x _ ) = x
extractRecordField (FieldTail prf') (RecCons _ xs) = extractRecordField prf' xs

--------------------------------------------------------------------------------

-- proof that a signature is a subset of another
public export
data SubSig : List Name -> Sig -> Type where
  SubSigNil  : SubSig Nil sig
  SubSigCons : {name : Name} -> FieldOf name sig -> SubSig rest sig -> SubSig (name :: rest) sig

-- constructs such a proof
public export
isSubSig : (names : List Name) -> (sig : Sig) -> Maybe (SubSig names sig)
isSubSig Nil            _   = Just SubSigNil
isSubSig (name :: rest) sig = case isFieldOf name sig of
  Nothing  => Nothing
  Just prf => case isSubSig rest sig of
    Nothing   => Nothing
    Just prfs => Just (SubSigCons prf prfs)

-- constructs the sub-signature
public export
subSig : SubSig names sig -> Sig
subSig SubSigNil             = Nil
subSig (SubSigCons prf rest) = lookupField prf :: subSig rest

-- projection function corresponding to a sub-signature
public export
projectSig : (prf : SubSig names sig) -> Rec sig -> Rec (subSig prf)
projectSig prf rec = case prf of
  SubSigNil            => RecNil
  SubSigCons this rest => RecCons (extractRecordField this rec) (projectSig rest rec)

--------------------------------------------------------------------------------
-- equality  for our universe (hackety hack hack...)

public export
TyEq : Ty -> Type
TyEq ty = Eq (reflectTy ty)

nilRecEq : Eq (Rec Nil)
nilRecEq = theEq (Rec Nil)

-- conbines the eq instance of the first element with the eq instance of the rest
consRecEq : Eq (reflectTy ty) -> Eq (Rec rest) -> Eq (Rec (MkField name ty :: rest))
consRecEq eq eqs = mkEq f where

  f : Rec (MkField name ty :: rest) -> Rec (MkField name ty :: rest) -> Bool
  f (RecCons x xs) (RecCons y ys) = case (==) @{eq} x y of
    False => False
    True  => (==) @{eqs} xs ys

-- proof that all types in a signature have Eq implemented
public export
data SigEq : Sig -> Type where
  SigEqNil  : SigEq Nil
  SigEqCons : TyEq ty -> SigEq rest -> SigEq (MkField name ty :: rest)

public export
sigEqToRecEq : SigEq sig -> Eq (Rec sig)
sigEqToRecEq sigEq = case sigEq of
  SigEqNil            => nilRecEq 
  SigEqCons this rest => consRecEq this (sigEqToRecEq rest)

mutual 

  -- construct such a proof
  public export
  mbSigEq : (sig : Sig) -> Maybe (SigEq sig)
  mbSigEq Nil = Just SigEqNil
  mbSigEq (MkField name ty :: rest) = case mbTyEq ty of
    Nothing  => Nothing
    Just eq  => case mbSigEq rest of
      Nothing  => Nothing
      Just eqs => Just (SigEqCons eq eqs)
  
  public export
  mbTyEq : (ty : Ty) -> Maybe (TyEq ty)
  mbTyEq IntT       = Just $ theEq Int   
  mbTyEq BoolT      = Just $ theEq Bool  
  mbTyEq StringT    = Just $ theEq String
  mbTyEq (FunT _ _) = Nothing
  mbTyEq (RecT sig) = case mbSigEq sig of
    Nothing    => Nothing
    Just sigEq => Just (sigEqToRecEq sigEq)

--------------------------------------------------------------------------------
-- comparison for our universe

public export
TyOrd : Ty -> Type
TyOrd ty = Ord (reflectTy ty)

nilRecOrd : Ord (Rec Nil)
nilRecOrd = theOrd (Rec Nil)

-- conbines the Ord instance of the first element with the Ord instance of the rest
consRecOrd : Ord (reflectTy ty) -> Ord (Rec rest) -> Ord (Rec (MkField name ty :: rest))
consRecOrd ord ords = mkOrd f g where

  f : Rec (MkField name ty :: rest) -> Rec (MkField name ty :: rest) -> Bool
  f (RecCons x xs) (RecCons y ys) = case (==) @{eqFromOrd ord} x y of
    False => False
    True  => (==) @{eqFromOrd ords} xs ys

  g : Rec (MkField name ty :: rest) -> Rec (MkField name ty :: rest) -> Ordering
  g (RecCons x xs) (RecCons y ys) = case compare@{ord} x y of
    LT => LT
    GT => GT
    EQ => compare @{ords} xs ys

-- proof that all types in a signature have Ord implemented
public export
data SigOrd : Sig -> Type where
  SigOrdNil  : SigOrd Nil
  SigOrdCons : TyOrd ty -> SigOrd rest -> SigOrd (MkField name ty :: rest)

public export
sigOrdToRecOrd : SigOrd sig -> Ord (Rec sig)
sigOrdToRecOrd sigOrd = case sigOrd of
  SigOrdNil            => nilRecOrd 
  SigOrdCons this rest => consRecOrd this (sigOrdToRecOrd rest)

mutual 

  -- construct such a proof
  public export
  mbSigOrd : (sig : Sig) -> Maybe (SigOrd sig)
  mbSigOrd Nil = Just SigOrdNil
  mbSigOrd (MkField name ty :: rest) = case mbTyOrd ty of
    Nothing   => Nothing
    Just ord  => case mbSigOrd rest of
      Nothing   => Nothing
      Just ords => Just (SigOrdCons ord ords)
  
  public export
  mbTyOrd : (ty : Ty) -> Maybe (TyOrd ty)
  mbTyOrd IntT       = Just $ theOrd Int   
  mbTyOrd BoolT      = Just $ theOrd Bool  
  mbTyOrd StringT    = Just $ theOrd String
  mbTyOrd (FunT _ _) = Nothing
  mbTyOrd (RecT sig) = case mbSigOrd sig of
    Nothing     => Nothing
    Just sigOrd => Just (sigOrdToRecOrd sigOrd)

--------------------------------------------------------------------------------
