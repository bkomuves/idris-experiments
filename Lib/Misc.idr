
-- miscellanaous useful functions

module Lib.Misc

import Data.Fin
import Data.List
import Data.Vect

%hide Data.Fin.Equality.FZ
%hide Data.Fin.Equality.FS

--------------------------------------------------------------------------------
-- transport

public export
transport : (0 refl : a = b) -> a -> b
transport Refl x = x

-- we want to refer to this, but for some reason, we cannot refer to it as (->)...
IdrisFunType : Type -> Type -> Type
IdrisFunType a b = a -> b

--------------------------------------------------------------------------------
-- List

public export
sortOn : Ord b => (a -> b) -> List a -> List a
sortOn f = sortBy (\x,y => compare (f x) (f y))

--------------------------------------------------------------------------------
-- Fin
public export
enumerateFin : (n : Nat) -> List (Fin n)
enumerateFin Z     = Nil
enumerateFin (S m) = FZ :: map FS (enumerateFin m)

--------------------------------------------------------------------------------
-- String

public export
intercalate : String -> List String -> String
intercalate sep = fastConcat . go where  
  go : List String -> List String
  go []      = []
  go (x::[]) = [x]
  go (x::xs) = x :: sep :: go xs

public export
intercalateLeft : String -> List String -> String
intercalateLeft sep [] = ""
intercalateLeft sep xs = sep ++ intercalate sep xs

--------------------------------------------------------------------------------
-- Eq

-- the default Eq instance of a type
public export
theEq : (a : Type) -> Eq a => Eq a
theEq _ @{eq} = eq

-- creates an Eq implementation from an equality check function
public export
mkEq : (a -> a -> Bool) -> Eq a
mkEq f = MkEq f (\x,y => not (f x y))

--------------------------------------------------------------------------------
-- Ord

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
-- Show

theShow : (a : Type) -> Show a => Show a
theShow _ @{show} = show

-- creates a Show implementation from `showPrec`
public export
mkShow : (Prec -> a -> String) -> Show a
mkShow f = MkShow (f Open) f

--------------------------------------------------------------------------------
-- Monad

public export
mapM : Traversable t => Applicative f => (a -> f b) -> t a -> f (t b)
mapM = traverse

--------------------------------------------------------------------------------
-- dependent vectors

-- dependent vector
public export
depVec : (n : Nat) -> (b -> Type) -> Vect n b -> Type
depVec n family xs = (i : Fin n) -> family (index i xs)

-- dependent monadic vector
public export
depVecM : (monad : Type -> Type) -> Monad monad => (n : Nat) -> (b -> Type) -> Vect n b -> Type
depVecM monad n family xs = (i : Fin n) -> monad (family (index i xs))

-- cons of a dependent vector
depCons : {n : Nat} -> {b : Type}
       -> {x : b} -> {xs : Vect n b}
       -> (family : b -> Type) 
       -> family x
       -> depVec n     family xs 
       -> depVec (S n) family (x::xs) 
depCons family y ys = \i => case i of
  FZ     => y
  (FS j) => ys j

-- sequencing of a dependent monadic vector
export
depSequence : (monad : Type -> Type) -> Monad monad => {n : Nat} -> (b : Type) -> (family : b -> Type) 
            -> (xs : Vect n b) -> depVecM monad n family xs -> monad (depVec n family xs) 
depSequence monad {n} b family xs mvec = worker n xs mvec where

  worker : (n : Nat) -> (xs : Vect n b) -> depVecM monad n family xs -> monad (depVec n family xs)
  worker n tvec mvec = case n of
    Z    => pure $ \i => absurd i
    S n1 => case tvec of
      (t::ts) => do
        y  <- mvec FZ
        ys <- worker n1 ts (\k => mvec (FS k))
        pure $ depCons family y ys

--------------------------------------------------------------------------------
