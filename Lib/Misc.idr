
-- miscellanaous useful functions

module Lib.Misc

import Data.List

--------------------------------------------------------------------------------

public export
sortOn : Ord b => (a -> b) -> List a -> List a
sortOn f = sortBy (\x,y => compare (f x) (f y))

--------------------------------------------------------------------------------

public export
intercalate : String -> List String -> String
intercalate sep = fastConcat . go where  
  go : List String -> List String
  go []      = []
  go (x::[]) = [x]
  go (x::xs) = x :: sep :: go xs

--------------------------------------------------------------------------------

-- the default Eq instance of a type
public export
theEq : (a : Type) -> Eq a => Eq a
theEq _ @{eq} = eq

-- creates an Eq implementation from an equality check function
public export
mkEq : (a -> a -> Bool) -> Eq a
mkEq f = MkEq f (\x,y => not (f x y))

--------------------------------------------------------------------------------

-- the default Ord instance of a type
public export
theOrd : (a : Type) -> Ord a => Ord a
theOrd _ @{ord} = ord

public export
eqFromOrd : Ord a -> Eq a
eqFromOrd ord = case ord of
  MkOrd @{eq} _ _ _ _ _ _ _ => eq

-- creates an Ord implementation from a comparison function
public export
mkOrd : (a -> a -> Bool) -> (a -> a -> Ordering) -> Ord a
mkOrd eq cmp = MkOrd @{mkEq eq} cmp lt gt le ge max min where
  lt  : a -> a -> Bool
  gt  : a -> a -> Bool
  le  : a -> a -> Bool
  ge  : a -> a -> Bool
  max : a -> a -> a
  min : a -> a -> a  
  lt  x y = cmp x y == LT
  gt  x y = cmp x y == GT
  le  x y = cmp x y /= GT
  ge  x y = cmp x y /= LT
  max x y = if ge x y then x else y
  min x y = if le x y then x else y

--------------------------------------------------------------------------------
