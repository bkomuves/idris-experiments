
-- | Modelling SQL queries

module SQL.Query

import Decidable.Equality
import Data.List

import SQL.Sig
import SQL.Expr

--------------------------------------------------------------------------------
-- database schema

-- schema of a single table
public export
data DBTable : Type where
  MkDBTable : Name -> Sig -> DBTable

public export
tableSig : DBTable -> Sig
tableSig (MkDBTable _ sig) = sig

public export
DBSchema : Type
DBSchema = List DBTable

-- proof that a table is present in a database
public export
data TableOf : Name -> DBSchema -> Type where
  TableHead : {table  : DBTable } -> TableOf name (table :: schema)
  TableTail : {schema : DBSchema} -> TableOf name schema -> TableOf name (table :: schema)

-- constructs such a proof
public export
isTableOf : (name : Name) -> (schema : DBSchema) -> Maybe (TableOf name schema)
isTableOf name Nil = Nothing
isTableOf name (MkDBTable n sig :: rest) = case decEq n name of
  Yes Refl => Just TableHead 
  No  _    => case isTableOf name rest of
    Nothing   => Nothing
    Just prf' => Just (TableTail prf')

-- looks up the signature of a table in database
public export
lookupTable : TableOf name schema -> DBTable
lookupTable (TableHead {table}) = table
lookupTable (TableTail prf'   ) = lookupTable prf'

-- looks up the signature of a table in database
public export
lookupTableSig : TableOf name schema -> Sig
lookupTableSig = tableSig . lookupTable

-- we can test it this way
public export
mbLookupTable : Name -> DBSchema -> Maybe DBTable
mbLookupTable name schema = case isTableOf name schema of
  Nothing  => Nothing
  Just prf => Just (lookupTable prf)

--------------------------------------------------------------------------------
-- something like an SQL SELECT query

public export
data Select : DBSchema -> Sig -> Type where

  -- a whole table (FROM)
  Table   : {name : Name} -> (prf : TableOf name db) -> Select db (lookupTableSig prf)

  -- select some columns (maybe in a different order) (SELECT)
  Project : {old : Sig} -> {names : List Name} -> (prf : SubSig names old) -> Select db old -> Select db (subSig prf)

  -- filters based on a condition (WHERE)
  Filter : {sig : Sig} -> (Rec sig -> Bool) -> Select db sig -> Select db sig

  -- more general function application (projection is a special case)
  Apply : {old : Sig} -> {new : Sig} -> (Rec old -> Rec new) -> Select db old -> Select db new

  -- order by (ORDER BY)
  OrderBy : Ord a => (Rec sig -> a) -> Select db sig -> Select db sig

--------------------------------------------------------------------------------

-- an actual database containing data
public export
data DB : DBSchema -> Type where
  EmptyDB : DB Nil
  ConsDB  : {name : Name} -> DataSet sig -> DB schema -> DB (MkDBTable name sig :: schema)

-- look up a dataset in a database
lookupDataSet : DB schema -> (prf : TableOf name schema) -> DataSet (lookupTableSig prf)
lookupDataSet (ConsDB dset _) (TableHead     ) = dset
lookupDataSet (ConsDB _ rest) (TableTail prf') = lookupDataSet rest prf'

-- execute a SELECT query
public export
execSelect : DB schema -> Select schema sig -> DataSet sig
execSelect db query = case query of

  Table   prf   => lookupDataSet db prf
  Project prf q => map (projectSig prf) $ execSelect db q
  Filter  fun q => filter fun $ execSelect db q
  Apply   fun q => map    fun $ execSelect db q 
  OrderBy fun q => sortBy (\x, y => compare (fun x) (fun y)) $ execSelect db q

--------------------------------------------------------------------------------

-- untyped SELECT query
public export
data RawSelect : Type where
  RawTable   : Name       -> RawSelect
  RawProject : List Name  -> RawSelect -> RawSelect 
  RawFilter  : RawExpr    -> RawSelect -> RawSelect
  RawApply   : RawExpr    -> RawSelect -> RawSelect
  RawOrderBy : RawExpr    -> RawSelect -> RawSelect

--------------------------------------------------------------------------------

-- cast non-record types to anonymous records (because in the database context 
-- we assume everything is a record)
castToRecord : (ty : Ty) -> (sig : Sig ** (reflectTy ty -> Rec sig))
castToRecord ty = case ty of
  RecT sig => (sig ** id)
  _        => ([MkField "_" ty] ** (\x => RecCons x RecNil))

--------------------------------------------------------------------------------

-- validate a raw SELECT query against a database schema
public export
validateSelect : (schema : DBSchema) -> RawSelect -> Maybe (sig : Sig ** Select schema sig)
validateSelect schema raw = go raw where

  go : RawSelect -> Maybe (sig : Sig ** Select schema sig)
  go raw = case raw of

    RawTable name => case isTableOf name schema of 
      Nothing  => Nothing
      Just prf => Just (lookupTableSig prf ** Table prf)

    RawProject names q => case go q of
      Nothing => Nothing
      Just (sig ** select) => case isSubSig names sig of
        Nothing  => Nothing
        Just prf => Just (subSig prf ** Project prf select) 

    RawFilter rawExpr q => case go q of
      Nothing => Nothing
      Just (sig ** select) => case typeCheckRawExpr sig rawExpr of
        Nothing => Nothing
        Just (ty ** expr) => case ty of
          BoolT => Just (sig ** Filter (runExpr expr) select)
          _     => Nothing

    RawApply rawExpr q => case go q of
      Nothing => Nothing
      Just (old ** select) => case typeCheckRawExpr old rawExpr of
        Nothing => Nothing
        Just (ty ** expr) => case castToRecord ty of
          (new ** conv) => Just (new ** Apply {old} {new} (conv . runExpr expr) select)
          _             => Nothing

    RawOrderBy rawExpr q => case go q of
      Nothing => Nothing
      Just (sig ** select) => case typeCheckRawExpr sig rawExpr of
        Nothing => Nothing
        Just (ty ** expr) => case mbTyOrd ty of
          Nothing  => Nothing
          Just ord => Just (sig ** OrderBy @{ord} (runExpr expr) select)

--------------------------------------------------------------------------------

