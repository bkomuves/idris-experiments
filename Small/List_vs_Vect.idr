
-- the isomorphism between lists and vectors

module Small.List_vs_Vect

import Builtin
import Data.List
import Data.Vect

--------------------------------------------------------------------------------

pred : Nat -> Nat
pred (S n) = n
pred Z     = Z

export
vectToList : Vect n a -> (list : List a ** length list = n)
vectToList Nil       = (Nil ** Refl)
vectToList (x :: xs) = case vectToList xs of
  (ys ** prf) => (x :: ys ** cong S prf) 

export
listToVec : {n : Nat} -> (list : List a ** length list = n) -> Vect n a
listToVec {n} dpair = case dpair of
  (list ** prf) => case list of
    Nil       => case prf of Refl => Nil
    (x :: xs) => case n of
      S m => let prf' = cong pred prf in (x :: listToVec (xs ** prf'))

--------------------------------------------------------------------------------
