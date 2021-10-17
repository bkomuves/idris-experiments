
-- poly-kinded fixpoint operator (not the most general one, to keep it simple)

--------------------------------------------------------------------------------

{-

we want to emulate this, with a single parametric datatype:

data Fix0 : (f : Type -> Type) -> Type where
  MkFix0 : f (Fix0 f) -> Fix0 f

data Fix1 : (f : Type -> Type -> Type) -> Type -> Type where
  MkFix1 : f (Fix1 f x) x -> Fix1 f x

data Fix2 : (f : Type -> Type -> Type -> Type) -> Type -> Type -> Type where
  MkFix2 : f (Fix2 f x y) x y -> Fix2 f x y

...

data ListF list a = NilF | ConsF a list

MyList : Type -> Type
MyList = Fix1 ListF

-}

module Small.Fix

import Data.Fin
import Data.Vect

--------------------------------------------------------------------------------
-- the idea is that we uncurry the second part of `Fix` into a product

-- creates the type `Type -> Type -> Type -> Type` with n arrows
F : Nat -> Type
F  Z    = Type
F (S n) = Type -> F n

-- creates the type `Type x Type x Type` with n components, implemented as a function
XS : Nat -> Type
XS n = Fin n -> Type

-- prepends an element
consXS : Type -> XS n -> XS (S n)
consXS x xs = \i => case i of
  FZ   => x
  FS j => xs j

-- applies (x,y,z,...) to f, resulting in a type for example:
-- 
-- > appF {n=2} Either (fromYS [Int,Bool]) = Either Int Bool 
--
appF : {n : Nat} -> F n -> XS n -> Type
appF {n=Z  } f _  = f
appF {n=S m} f xs = appF (f $ xs 0) $ \i => xs (FS i)

-- currying n-ary type constructors
curry : {n : Nat} -> (XS n -> Type) -> F n
curry {n=Z  } h = h absurd
curry {n=S m} h = \x => curry {n=m} (\xs => h (consXS x xs))

-- uncurrying n-ary type constructors
uncurry : {n : Nat} -> F n -> (XS n -> Type)
uncurry = appF

--------------------------------------------------------------------------------
-- convenience feature for testing in the REPL

-- creates the type `Type x Type x Type` with n components, implemented as a vector (for convenience)
YS : Nat -> Type
YS n = Vect n Type

-- converts YS to XS
fromYS : YS n -> XS n
fromYS ys i = index i ys

--------------------------------------------------------------------------------
-- the type of the Fix type constructor

-- the standard type of the n-ary fixpoint type constructor (curried version)
FixType : Nat -> Type
FixType n = F (S n) -> F n

-- an alternative type for the n-ary fixpoint constructor (uncurried version)
FixTypeB : Nat -> Type
FixTypeB n = F (S n) -> XS n -> Type

curryFix : {n : Nat} -> FixTypeB n -> FixType n
curryFix h = \u => curry (h u)

uncurryFix : {n : Nat} -> FixType n -> FixTypeB n
uncurryFix u f xs = appF (u f) xs 

--------------------------------------------------------------------------------
-- uncurried fixpoint data type

appFixB : {n : Nat} -> (fix : FixTypeB n) -> (f : F (S n)) -> (xs : XS n) -> Type
appFixB fix f xs = fix f xs

fAppFixB : {n : Nat} -> (fix : FixTypeB n) -> (f : F (S n)) -> (xs : XS n) -> Type
fAppFixB fix f xs = appF f $ consXS (appFixB fix f xs) xs

data FixB : (n : Nat) -> (f : F (S n)) -> (xs : XS n) -> Type where
  Wrap : fAppFixB {n} (FixB n) f xs -> FixB n f xs

--------------------------------------------------------------------------------
-- curried (standard) fixpoint data type

-- applies f and then (x,y,z...) to Fix, resulting in `fix f x y z...`
appFix : {n : Nat} -> (fix : FixType n) -> (f : F (S n)) -> (xs : XS n) -> Type
appFix fix f xs = appF (fix f) xs

-- computes `f (fix f x y z...) x y z....`
fAppFix : {n : Nat} -> (fix : FixType n) -> (f : F (S n)) -> (xs : XS n) -> Type
fAppFix fix f xs = appF f $ consXS (appFix fix f xs) xs

Fix : (n : Nat) -> FixType n
Fix n = curryFix (FixB n)

--------------------------------------------------------------------------------
-- example

data ListF list a = NilF | ConsF a list

L : Type -> Type
L = Fix 1 ListF

toL : List a -> L a
toL Nil     = Wrap NilF
toL (x::xs) = Wrap (ConsF x (toL xs))

fromL : L a -> List a
fromL (Wrap l) = case l of
  NilF       => Nil
  ConsF x xs => x :: fromL xs
  
--------------------------------------------------------------------------------
