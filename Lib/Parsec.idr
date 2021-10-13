
-- minimalistic Parsec-style parser combinator lib

module Lib.Parsec

import Data.String

--------------------------------------------------------------------------------

public export
Msg : Type
Msg = String

data Result : Type -> Type -> Type where
  Ok   : a -> List tok -> Result tok a      -- success
  Fail : Result tok a                       -- backtracking failure
  Err  : Msg -> Result tok a                -- unrecoverable failure

Functor (Result tok) where
  map f res = case res of
    Ok x rem => Ok (f x) rem
    Fail     => Fail
    Err err  => Err err

export
data Parser : Type -> Type -> Type where 
  MkParser : (List tok -> Result tok a) -> Parser tok a

public export
Lexer : Type -> Type
Lexer a = Parser Char a

--------------------------------------------------------------------------------

export
pPure : a -> Parser tok a
pPure x = MkParser (\ts => Ok x ts)

export
pMap : (a -> b) -> Parser tok a -> Parser tok b
pMap f (MkParser p) = MkParser $ \toks => case p toks of
  Ok x rem => Ok (f x) rem
  Fail     => Fail
  Err err  => Err err

export
pBind : Parser tok a -> (a -> Parser tok b) -> Parser tok b
pBind (MkParser p) f = MkParser $ \toks => case p toks of
  Err err  => Err err
  Fail     => Fail
  Ok x rem => case f x of
    MkParser q => q rem

export
pApStrict : Parser tok (a -> b) -> Parser tok a -> Parser tok b
pApStrict u x = pBind u (\f => pMap f x)

export
pApLazy : Parser tok (a -> b) -> Lazy (Parser tok a) -> Parser tok b
pApLazy (MkParser p) qq = MkParser $ \toks => case p toks of
  Fail     => Fail
  Err err  => Err err
  Ok f rem => case qq of
    MkParser q => case q rem of
      Ok x rem' => Ok (f x) rem'
      Fail      => Fail
      Err err   => Err err

infixl 2 <*>|
export
(<*>|) : Parser tok (a -> b) -> Lazy (Parser tok a) -> Parser tok b
(<*>|) = pApLazy 

export
pFail : Parser tok a
pFail = MkParser (\_ => Fail)

export
pErr : Msg -> Parser tok a
pErr msg = MkParser (\_ => Err msg)

pAlter : Parser tok a -> Lazy (Parser tok a) -> Parser tok a
pAlter (MkParser p) (MkParser q) = MkParser $ \toks => case p toks of
  Ok x rem => Ok x rem
  Err err  => Err err
  Fail     => q toks

export
pEOF : Parser tok Unit
pEOF = MkParser (\toks => case toks of
  [] => Ok MkUnit []
  _  => Fail)

--------------------------------------------------------------------------------

public export
Functor (Parser tok) where
  map = pMap

public export
Applicative (Parser tok) where
  pure  = pPure 
  (<*>) = pApStrict

public export
Monad (Parser tok) where
  (>>=) = pBind

public export
Alternative (Parser tok) where
  empty = pFail
  (<|>) = pAlter 

--------------------------------------------------------------------------------

export
runParser : Parser tok a -> List tok -> Either Msg a
runParser (MkParser p) ts = case p ts of
  Fail     => Left "parser failure"
  Err msg  => Left msg
  Ok y rem => case rem of
    [] => Right y
    _  => Left "unexpected end of input"

export
runLexer : Lexer a -> String -> Either Msg a
runLexer lexer input = runParser lexer (unpack input)

export
accept : (tok -> Maybe a) -> Parser tok a
accept f = MkParser $ \toks => case toks of
  []      => Fail
  (t::ts) => case f t of
    Nothing => Fail
    Just y  => Ok y ts

export
pWhen : (tok -> Bool) -> Parser tok tok
pWhen cond = accept (\t => if cond t then Just t else Nothing)

export
pJust : Parser tok (Maybe a) -> Parser tok a
pJust p = p >>= \mb => case mb of
  Just x  => pure x
  Nothing => pFail

pEither : Parser tok a -> Parser tok b -> Parser tok (Either a b)
pEither p q = map Left p <|> map Right q

--------------------------------------------------------------------------------

export
oneOf : Eq tok => List tok -> Parser tok tok
oneOf list = pWhen (\t => elem t list)

export
noneOf : Eq tok => List tok -> Parser tok tok
noneOf list = pWhen (\t => not (elem t list)) 

export
lookahead : Parser tok a -> Parser tok (Maybe a)
lookahead (MkParser p) = MkParser $ \toks => case p toks of
  Ok x _  => Ok (Just x) toks
  Fail    => Ok Nothing  toks
  Err msg => Err msg

export
option : Parser tok a -> Parser tok (Maybe a)
option (MkParser p) = MkParser $ \toks => case p toks of
  Ok x ts => Ok (Just x) ts
  Fail    => Ok Nothing  toks
  Err msg => Err msg

export
optional : a -> Parser tok a -> Parser tok a
optional x0 p = pMap (\mb => case mb of 
  Nothing => x0 
  Just x  => x) (option p)

mutual

  export
  many : Parser tok a -> Parser tok (List a)
  many p = (some p) <|> pure Nil 
  
  export
  some : Parser tok a -> Parser tok (List a)
  some p = ((::) <$> p <*>| many p)  -- this version causes an infinite loop if `<*>` is strict?

export
openCloseSepBy : Parser t left -> Parser t right -> Parser t sep -> Parser t a -> Parser t (List a)
openCloseSepBy l r s p = do
  _  <- l
  ei <- pEither r p
  case ei of
    Left  _ => pure Nil
    Right x => do
      xs <- many (s >>= \_ => p)
      _  <- r
      pure (x::xs)

--------------------------------------------------------------------------------

export
anyChar : Lexer Char
anyChar = accept Just

export
char : Char -> Lexer Char
char d = accept (\c => if (c==d) then Just c else Nothing)

export
digit : Lexer Char
digit = accept (\c => if (c >= '0' && c <= '9') then Just c else Nothing)

export
lower : Lexer Char
lower = accept (\c => if (c >= 'a' && c <= 'z') then Just c else Nothing)

export
upper : Lexer Char
upper = accept (\c => if (c >= 'A' && c <= 'Z') then Just c else Nothing)

export
letter : Lexer Char
letter = lower <|> upper

export
alphaNum : Lexer Char
alphaNum = letter <|> digit

export
alphaNumUnderscore : Lexer Char
alphaNumUnderscore = alphaNum <|> char '_'

export
space : Lexer Char
space = char ' '

export
newline : Lexer Unit
newline = do
  _ <- option (char '\x0d') 
  _ <- char '\x0a' 
  pure MkUnit

export
underscore : Lexer Char
underscore = char '_'

export
comma : Lexer Char
comma = char ','

--------------------------------------------------------------------------------

export
oneOfChars : String -> Lexer Char
oneOfChars str = oneOf (unpack str)

export
noneOfChars : String -> Lexer Char
noneOfChars str = noneOf (unpack str)

export
spaces1 : Lexer Unit
spaces1 = some space >>= (\_ => pure MkUnit)

export
spaces0 : Lexer Unit
spaces0 = many space >>= (\_ => pure MkUnit)

export
whitespace : Lexer Unit
whitespace = many (spaces1 <|> newline) >>= (\_ => pure MkUnit)

export
preWhite : Lexer a -> Lexer a
preWhite p = whitespace *> p

export
postWhite : Lexer a -> Lexer a
postWhite p = p <* whitespace

export
postSpaces : Lexer a -> Lexer a
postSpaces p = p <* spaces0

export
digits : Lexer String
digits = map pack $ some digit

export
identifier : Lexer String
identifier = map pack $ some alphaNumUnderscore

--------------------------------------------------------------------------------

export
natural : Lexer Integer
natural = digits >>= \s => case parsePositive s of
  Just n  => pPure n
  Nothing => pErr "natural: shouldn't happen"

export
integer : Lexer Integer
integer = do
  sgn <- optional '+' (oneOfChars "+-")
  ds  <- digits
  case parseInteger (singleton sgn ++ ds) of
    Just n  => pPure n
    Nothing => pErr "integer: shouldn't happen"

escapedChar : Char -> Lexer Char
escapedChar z = do
  c <- pWhen (\c => c /= z)
  if (c /= '\\')
    then pure c
    else do
      d <- anyChar
      pure $ case d of
        'n' => '\n'
        'r' => '\r'
        't' => '\t'
        'b' => '\b'
        'f' => '\f'
        'v' => '\v'
        '0' => '\0'
        _   => d

escaped : Char -> Lexer String
escaped z = pMap pack $ many (escapedChar z)

-- note: we omit the quotes
export
stringLit : Lexer String
stringLit = do
  _  <- char    '"'
  cs <- escaped '"'
  _  <- char    '"'
  pure cs

--------------------------------------------------------------------------------
