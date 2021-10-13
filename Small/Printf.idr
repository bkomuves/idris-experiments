
-- type-safe sprintf

module Small.Printf

import Data.String

--------------------------------------------------------------------------------

public export
Renderer : Type
Renderer = (t : Type ** (t -> String))

public export
data FmtEntry
  = FmtChar Char
  | FmtVar  Renderer

public export
Formatter : Type
Formatter = List FmtEntry

public export
charToRender : Char -> Renderer
charToRender 'i' = (Int    ** show     )  
charToRender 'c' = (Char   ** singleton)
charToRender 's' = (String ** id       )
charToRender 'b' = (Bool   ** show     )
charToRender _   = (Void   ** absurd   )

public export
parseFmtString1 : List Char -> Formatter
parseFmtString1 = go where

  go : List Char -> Formatter
  go fmt = case fmt of
    Nil     => Nil
    (c::cs) => if c /= '%'
      then FmtChar c :: go cs 
      else case cs of
        Nil     => FmtVar (Void ** absurd) :: Nil 
        (d::ds) => FmtVar (charToRender d) :: go ds

public export
parseFmtString : String -> Formatter
parseFmtString s = parseFmtString1 (unpack s)

--------------------------------------------------------------------------------

public export
FormatFunType : Formatter -> Type -> Type
FormatFunType Nil                 result = result
FormatFunType (FmtChar _ :: rest) result =          FormatFunType rest result
FormatFunType (FmtVar  p :: rest) result = fst p -> FormatFunType rest result

-- NB.: "prefix" is not a valid variable name!!!
public export
formatPrepend : String -> (fmt : Formatter) -> FormatFunType fmt String -> FormatFunType fmt String
formatPrepend prefix_ Nil                 s = (prefix_ ++ s)
formatPrepend prefix_ (FmtChar _ :: rest) s =       formatPrepend prefix_ rest s
formatPrepend prefix_ (FmtVar  p :: rest) f = \x => formatPrepend prefix_ rest (f x)

public export
format : (fmt : Formatter) -> FormatFunType fmt String
format fmt = go fmt where

  go : (fmt : Formatter) -> FormatFunType fmt String
  go fmt = case fmt of
    Nil     => ""
    (e::es) => case e of
      FmtChar c =>       formatPrepend (singleton c) es (go es) 
      FmtVar  p => \x => formatPrepend (snd p x)     es (go es)

--------------------------------------------------------------------------------

public export
PrintfType1 : List Char -> Type -> Type
PrintfType1 fmt result = FormatFunType (parseFmtString1 fmt) result

public export
PrintfType : String -> Type -> Type
PrintfType fmt result = PrintfType1 (unpack fmt) result

public export
sprintf1 : (fmt : List Char) -> PrintfType1 fmt String
sprintf1 fmt = format (parseFmtString1 fmt)

public export
sprintf : (fmt : String) -> PrintfType fmt String
sprintf fmt = format (parseFmtString1 (unpack fmt))

--------------------------------------------------------------------------------
