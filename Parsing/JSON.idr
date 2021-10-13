
-- parsing JSON strings into a schema-indexed JSON type (in two steps)

module Parsing.JSON

import Data.Maybe
import Data.List
import Data.String

import Decidable.Equality

import Lib.Parsec
import Lib.Misc

--------------------------------------------------------------------------------

public export
Number : Type
Number = Integer   -- Double

mutual 

  public export
  data JSON
    = JNull
    | JBool    Bool
    | JNumber  Number
    | JString  String
    | JArray   (List JSON)
    | JObject  (List KeyValue)

  public export
  record KeyValue where
    constructor MkKeyValue
    key   : String
    value : JSON

--------------------------------------------------------------------------------
-- Show instance

mutual

  Show JSON where
    show json = case json of
      JNull     => "null"
      JBool   b => if b then "true" else "false"
      JNumber n => show n
      JString s => show s
      JArray  l => "[" ++ intercalate ", " (map show l) ++ "]"
      JObject o => "{" ++ intercalate ", " (map show o) ++ "}"
  
  Show KeyValue where
    show kv = show kv.key ++ ": " ++ show kv.value

--------------------------------------------------------------------------------

-- a type describing the schema of a JSON file.
-- Note: unlike traditional JSON, we only allow homogeneous arrays!

mutual

  public export
  data Ty    
    = BoolTy
    | NumberTy
    | StringTy
    | ArrayTy  Ty
    | ObjectTy Sig
    | AnyTy               -- we need this for inferring types of null

  public export
  record Field where
    constructor MkField
    key  : String
    type : Ty

  public export
  Sig : Type
  Sig = List Field
  
  Show Ty where
    show ty = case ty of
      AnyTy        => "Any" 
      BoolTy       => "Bool"
      NumberTy     => "Number"
      StringTy     => "String"
      ArrayTy ty   => "Array[" ++ show ty ++ "]"
      ObjectTy sig => "Object{" ++ intercalate ", " (map show sig) ++ "}"

  Show Field where
    show fld = fld.key ++ ": " ++ show (fld.type)

--------------------------------------------------------------------------------

sortSig : Sig -> Sig
sortSig = sortOn (\x => x.key)

sortKVs : List KeyValue -> List KeyValue
sortKVs = sortOn (\x => x.key)

--------------------------------------------------------------------------------
-- decidable equality for types

mutual 

  DecEq Ty where
    decEq  AnyTy           AnyTy          = Yes Refl
    decEq  BoolTy          BoolTy         = Yes Refl
    decEq  NumberTy        NumberTy       = Yes Refl
    decEq  StringTy        StringTy       = Yes Refl

    decEq (ArrayTy ty1)   (ArrayTy ty2)   = case decEq ty1  ty2  of 
                                              Yes p => Yes (cong ArrayTy  p) 
                                              No  _ => No believe_me 

    decEq (ObjectTy sig1) (ObjectTy sig2) = case decEq sig1 sig2 of 
                                              Yes p => Yes (cong ObjectTy p) 
                                              No  _ => No believe_me 

    decEq _ _ = No believe_me        

  DecEq Field where
    decEq (MkField key1 ty1) (MkField key2 ty2) = case decEq key1 key2 of
      No  _ => No believe_me
      Yes p => case decEq ty1 ty2 of
        No  _ => No believe_me
        Yes q => Yes (cong2 MkField p q)

  Eq Ty where
    t1 == t2 = case decEq t1 t2 of { Yes _ => True ; No _ => False } 

  Eq Field where
    f1 == f2 = case decEq f1 f2 of { Yes _ => True ; No _ => False } 

--------------------------------------------------------------------------------

mutual

  public export
  data TyJSON : Ty -> Type where
    TNull   : (ty : Ty) -> TyJSON ty            -- null can stand in place of any value
    TBool   : Bool   -> TyJSON BoolTy
    TNumber : Number -> TyJSON NumberTy
    TString : String -> TyJSON StringTy
    TArray  : {ty  : Ty } -> List (TyJSON ty) -> TyJSON (ArrayTy ty)
    TObject : {sig : Sig} -> Rec sig -> TyJSON (ObjectTy sig) 

  public export
  data Rec : Sig -> Type where
    RecNil  : Rec Nil
    RecCons : {fld : Field} -> TyJSON (fld.type) -> Rec rest -> Rec (fld :: rest)

--------------------------------------------------------------------------------

-- if all of them are rights, then we extract them; otherwise we collect 
-- the lefts (interpreted as errors)
transposeRights : List (Either e a) -> Either (List e) (List a)
transposeRights = go where 

  mutual

    go : List (Either e a) -> Either (List e) (List a)
    go Nil = Right Nil
    go (this::rest) = case this of
      Right y => mapSnd (y::) (go rest)
      Left  e => Left (e :: goLeft rest)
  
    goLeft : List (Either e a) -> List e
    goLeft Nil = Nil
    goLeft (this::rest) = case this of
      Right _ =>      goLeft rest
      Left  e => e :: goLeft rest

    -- ex : List (Either Int Int)
    -- ex = [ Right 5, Left 9, Right 7, Left 11, Right 4 ]

--------------------------------------------------------------------------------
-- validates a raw JSON against a schema

data CheckErr 
  = TypeMismatch Ty JSON
  | BadArray Ty (List CheckErr)
  | BadField Field KeyValue
  | MissingOrExtraFields
  | CantCheckAgainstAny         -- the type of validateJSON does not work out when checking against AnyT...

mutual

  export
  validateJSON : (ty : Ty) -> JSON -> Either CheckErr (TyJSON ty)
  validateJSON ty             JNull         = Right (TNull  ty)
  validateJSON BoolTy         (JBool   b)   = Right (TBool   b)
  validateJSON NumberTy       (JNumber n)   = Right (TNumber n)
  validateJSON StringTy       (JString s)   = Right (TString s)
  validateJSON (ObjectTy sig) (JObject kvs) = mapSnd TObject $ validateObject sig kvs 
  validateJSON (ArrayTy  ty ) (JArray  xs)  = mapSnd TArray  $ validateArray  ty  xs
  validateJSON AnyTy          _             = Left CantCheckAgainstAny 
  validateJSON ty             json          = Left (TypeMismatch ty json)

  validateArray : (ty : Ty) -> List JSON -> Either CheckErr (List (TyJSON ty))
  validateArray ty list = case transposeRights $ map (validateJSON ty) list of
    Right arr => Right arr
    Left  bad => Left (BadArray ty bad)

  -- NOTE: for now, we don't allow reordering of fields...
  -- TODO: do this. It's a bit annoying, as we have to keep the Sig order
  validateObject : (sig : Sig) -> List KeyValue -> Either CheckErr (Rec sig)
  validateObject = worker where

    worker : (sig : Sig) -> List KeyValue -> Either CheckErr (Rec sig)
    worker  Nil          Nil          = Right RecNil
    worker (fld :: sig') (kv :: kvs') = if fld.key /= kv.key
      then Left (BadField fld kv)
      else case validateJSON fld.type kv.value of
        Left  err   => Left err
        Right tjson => mapSnd (RecCons tjson) (worker sig' kvs')
    worker _ _ = Left MissingOrExtraFields

--------------------------------------------------------------------------------

data InferErr
  = InhomogArray Ty Ty

inferJSON : JSON -> Either InferErr (ty : Ty ** TyJSON ty)
inferJSON = go where

  mutual

    go : JSON -> Either InferErr (ty : Ty ** TyJSON ty)
    go json = case json of

      JNull      => Right (AnyTy    ** TNull AnyTy)
      JBool    b => Right (BoolTy   ** TBool    b )
      JNumber  n => Right (NumberTy ** TNumber  n )
      JString  s => Right (StringTy ** TString  s )

      JArray   l => 
        let eis = map go l 
            ty  = guessArrayType eis
        in  case transposeArray ty eis of
              Left  err  => Left err
              Right list => Right (ArrayTy ty ** TArray list)

      JObject  o => case goObject o of
        Left err           => Left err
        Right (sig ** rec) => Right (ObjectTy sig ** TObject rec)

    goObject : List KeyValue -> Either InferErr (sig : Sig ** Rec sig)
    goObject Nil       = Right (Nil ** RecNil) 
    goObject (kv::kvs) = case go kv.value of
      Left  err        => Left err
      Right (ty ** u)  => case goObject kvs of
        Left  err         => Left err
        Right (sig ** us) => Right ((MkField kv.key ty :: sig) ** RecCons u us) 

    -- we want to allow nulls in otherwise homogeneous arrays..
    -- so first we find the first inferred type, and use that to check the other
    guessArrayType : List (Either InferErr (ty : Ty ** TyJSON ty)) -> Ty
    guessArrayType eis = 
      case mapMaybe f eis of
        Nil     => AnyTy
        (ty::_) => ty
      where 
        f : (Either InferErr (ty : Ty ** TyJSON ty)) -> Maybe Ty
        f (Right (ty ** _)) = if ty /= AnyTy then Just ty else Nothing
        f (Left  _        ) = Nothing

    transposeArray : (ty : Ty)
                  -> List (Either InferErr (ty : Ty ** TyJSON ty)) 
                  -> Either InferErr (List (TyJSON ty))
    transposeArray ty Nil = Right Nil
    transposeArray ty (ei :: rest) = case ei of
      Left  err      => Left err
      Right (t ** u) => case u of
        TNull _ => mapSnd ((TNull ty)::) $ transposeArray ty rest
        _       => case decEq ty t of
          Yes Refl => mapSnd (u::) $ transposeArray ty rest
          No  _    => Left (InhomogArray ty t)

--------------------------------------------------------------------------------
-- parsing strings into a raw JSON type

mutual

  jsonP : Lexer JSON
  jsonP = do
    _ <- whitespace
    postWhite (nullP <|> booleanP <|> numberP <|> stringP <|> arrayP <|> objectP)  

  nullP : Lexer JSON
  nullP = pJust $ do
    xs <- identifier
    pure $ case xs of
      "null" => Just JNull
      _      => Nothing 

  booleanP : Lexer JSON
  booleanP = pJust $ do
    xs <- identifier
    pure $ case xs of
      "true"  => Just (JBool True)
      "false" => Just (JBool False)
      _       => Nothing 

  numberP : Lexer JSON
  numberP = map JNumber integer

  stringP : Lexer JSON
  stringP = map JString stringLit

  arrayP : Lexer JSON
  arrayP = map JArray $ openCloseSepBy 
    (postWhite $ char '[') 
    (postWhite $ char ']')
    (postWhite $ char ',')
    jsonP

  objectP : Lexer JSON
  objectP = map JObject $ openCloseSepBy 
    (postWhite $ char '{') 
    (postWhite $ char '}')
    (postWhite $ char ',')
    keyValueP

  keyValueP : Lexer KeyValue
  keyValueP = do
    key <- postWhite stringLit
    _   <- postWhite (char ':')
    val <- postWhite jsonP
    pure (MkKeyValue key val)

-------------------------------------------------------------------------------

{-
test_string : String
test_string = "{\"list\":[null,6,17,null,99,103],\"bool\":true,\"string\":\"foobar\"}"

test_json : JSON
test_json = case runLexer jsonP test_string of
  Right j  => j
  Left  _  => believe_me 0

test_tyjson : (ty : Ty ** TyJSON ty)
test_tyjson = case inferJSON test_json of
  Right p  => p
  Left  _  => believe_me 0
-}
