
-- skew binary random access lists (a la Okasaki),
-- with worst case O(1) `cons` and O(log(k)) `lookup`

module Data.RAL 

import Data.Nat
import Data.Fin
import Data.Bits

%hide Prelude.toList

--------------------------------------------------------------------------------

fatal : String -> a
fatal msg = assert_total (idris_crash msg)

prec : Nat -> Nat
prec (S m) = m
prec  Z    = Z

subtract : Nat -> Nat -> Nat
subtract a b = integerToNat (natToInteger a - natToInteger b)

natShiftL : Nat -> Nat -> Nat
natShiftL x k = integerToNat $ shiftL (natToInteger x) k

--------------------------------------------------------------------------------
-- full binary trees

treeSize : Nat -> Nat
treeSize n = prec (natShiftL 2 n) 

-- complete binary tree with data on both nodes and leaves
-- we have `Cherry` to avoid the extra indirections at the bottom
data Tree : (0 n : Nat) -> Type -> Type where
  Leaf   : a -> Tree 0 a
  Cherry : a -> a -> a -> Tree 1 a
  Node   : {0 k : Nat} -> a -> Tree (S k) a -> Tree (S k) a -> Tree (S (S k)) a

build : {n : Nat} -> a -> Tree n a -> Tree n a -> Tree (S n) a
build {n} x s t = case n of
  0   => case s of { Leaf y => case t of { Leaf z => Cherry x y z } }
  S m => Node x s t

dismantle : {n : Nat} -> Tree (S n) a -> (a, Tree n a, Tree n a)
dismantle {n} t = case t of
  Cherry x y z => (x, Leaf y, Leaf z)
  Node   x s t => (x, s, t)

treeIndex : {n : Nat} -> Nat -> Tree n a -> a
treeIndex {n} i tree = case i of
  Z => case tree of
    Leaf   x     => x
    Cherry x _ _ => x
    Node   x _ _ => x
  S j => case tree of 
    Leaf  _        => fatal "treeIndex: out of range"
    Cherry   _ x y => case j of { 0 => x ; 1 => y ; _ => fatal "treeIndex: out of range" }
    Node {k} _ s t => let m = treeSize (S k) 
                      in  if j < m then treeIndex j s else treeIndex (subtract j m) t

safeTreeIndex : {n : Nat} -> Fin (treeSize n) -> Tree n a -> a
safeTreeIndex i tree = treeIndex (finToNat i) tree

treeToList : {0 n : Nat} -> Tree n a -> List a
treeToList (Leaf x)       = x :: Nil
treeToList (Cherry x y z) = x :: y :: z :: Nil
treeToList (Node x s t)   = x :: treeToList s ++ treeToList t

-- ex : Tree 2 Int
-- ex = Node 101 (Cherry 102 103 104) (Cherry 105 106 107)

--------------------------------------------------------------------------------

-- sequences of completely binary trees starting at level `n`
data Seq1 : Nat -> Type -> Type where
  Nil1  : Seq1 n a
  Skip1 : (skip : Nat) -> Tree (skip + n) a -> Seq1 (S (skip + n)) a -> Seq1 n a

||| `Seq a` is the type of sequences of elements of type `a` (isomorphic to `List a`)
export
data Seq : Type -> Type where
  Empty   : Seq a
  Start1  : (n : Nat) -> Tree n a             -> Seq1 (S n) a -> Seq a    -- first nonzero digit is 1
  Start2  : (n : Nat) -> Tree n a -> Tree n a -> Seq1 (S n) a -> Seq a    -- first nonzero digit is 2

--------------------------------------------------------------------------------

lookup1 : {n : Nat} -> Nat -> Seq1 n a -> Maybe a
lookup1 {n} i seq = case seq of
  Nil1         => Nothing
  Skip1 k t ts => 
    let m = treeSize (k+n)
    in  if i < m then Just (treeIndex i t) else lookup1 (subtract i m) ts

skip1 : Seq1 (S n) a -> Seq1 n a
skip1 Nil1          = Nil1
skip1 (Skip1 k t s) = Skip1 (S k) (rewrite lemma k n in t) (rewrite lemma k n in s) where

  lemma : (k, n : Nat) -> S (k + n) = k + S n 
  lemma  Z    n = Refl
  lemma (S j) n = cong S (lemma j n)

fromSeq1 : {n : Nat} -> Seq1 n a -> Seq a
fromSeq1 {n} seq1 = case seq1 of
  Nil1         => Empty
  Skip1 k t ts => Start1 (k+n) t ts

--------------------------------------------------------------------------------

||| Proof that a sequence is not empty
export 
data NonEmpty : Seq a -> Type where
  NonEmpty1 : NonEmpty (Start1 n t seq)
  NonEmpty2 : NonEmpty (Start2 n t1 t2 seq)

||| constructs such a proof, O(1)
isNonEmpty : (seq : Seq a) -> Maybe (NonEmpty seq)
isNonEmpty Empty            = Nothing
isNonEmpty (Start1 _ _ _)   = Just NonEmpty1
isNonEmpty (Start2 _ _ _ _) = Just NonEmpty2

--------------------------------------------------------------------------------

length1 : {n : Nat} -> Seq1 n a -> Nat
length1 {n}  Nil1           = 0
length1 {n} (Skip1 k _ seq) = treeSize (k+n) + length1 seq

||| length of the sequence, O(log(n))
export 
length : Seq a -> Nat
length seq = case seq of
  Empty             => 0
  Start1 n _   rest =>     treeSize n + length1 rest
  Start2 n _ _ rest => 2 * treeSize n + length1 rest

||| whether the sequence in empty, O(1)
null : Seq a -> Bool
null Empty = True
null _     = False

--------------------------------------------------------------------------------

lemma_plus1 : (m : Nat) -> plus m 1 = S m
lemma_plus1  Z    = Refl
lemma_plus1 (S k) = cong S (lemma_plus1 k)

lemma_plus_S2 : (m, n : Nat) -> plus m (S (S n)) = S (plus m (S n)) 
lemma_plus_S2 Z     _ = Refl
lemma_plus_S2 (S k) n = cong S (lemma_plus_S2 k n) 

--------------------------------------------------------------------------------

||| prepending an element, O(1)
export
cons : a -> Seq a -> Seq a
cons x seq = case seq of

  Empty => Start1 0 (Leaf x) Nil1

  -- first nonzero digit is one
  Start1 n t rest => case n of
    -- least significant digit is zero
    (S m) => Start1 0 (Leaf x) $ Skip1 m  
               (rewrite lemma_plus1 m in t) 
               (rewrite lemma_plus1 m in rest)
    -- least significant digit is one
    Z => case t of { Leaf y => Start2 0 (Leaf x) (Leaf y) rest }         

  -- first nonzero digit is two
  Start2 n t1 t2 rest => case rest of
    -- this was the last digit
    Nil1 => Start1 (S n) (build x t1 t2) Nil1       
    -- there are more digits agter
    Skip1 k tree trees => case k of   
      -- next digit is zero (now becoming 1)
      (S m) => Start1 (S n) (build x t1 t2) $ Skip1 m 
                 (rewrite lemma_plus_S2 m n in tree) 
                 (rewrite lemma_plus_S2 m n in trees)
      -- next digit is one (now becoming 2)
      Z     => Start2 (S n) (build x t1 t2) tree trees 

||| view from the left end, O(1)
export
unCons : Seq a -> Maybe (a, Seq a)
unCons seq = case seq of

  Empty => Nothing

  -- first nonzero digit is one
  Start1 n t rest => case n of
    -- least significant digit is zero (it comes from 00..0|20 -> 00..0|01)
    (S m) => case dismantle t of
      (x,s,t) => Just (x, Start2 m s t $ skip1 rest)
    -- least significant digit is one (it comes from 00..0|1x -> 10..0|1x)
    Z => case t of 
      Leaf y => case rest of
        Nil1         => Just (y, Empty)
        Skip1 k t ts => Just (y, Start1 (S k) 
          (rewrite sym (lemma_plus1 k) in t) 
          (rewrite sym (lemma_plus1 k) in ts))

  -- first nonzero digit is two 
  Start2 n t1 t2 rest => case n of
    -- it's the least significant digit (it comes from 1x... -> 2x...)
    Z => case t1 of { Leaf x => Just (x, Start1 Z t2 rest) }
    -- it's not the least significant digit (it comes from 00..0|21 -> 00..0|02)
    S m => case dismantle t1 of
      (x,s1,s2) => Just (x, Start2 m s1 s2 (Skip1 0 t2 rest))

--------------------------------------------------------------------------------

export 
mbHead : Seq a -> Maybe a
mbHead seq = fst <$> unCons seq

export 
mbTail : Seq a -> Maybe (Seq a)
mbTail seq = snd <$> unCons seq

export 
head : (seq : Seq a) -> {auto 0 prf : NonEmpty seq} -> a
head seq = case unCons seq of { Just (y,_) => y ; Nothing => fatal "head: impossible" }

export 
tail : (seq : Seq a) -> {auto 0 prf : NonEmpty seq} -> Seq a
tail seq = case unCons seq of { Just (_,t) => t ; Nothing => fatal "tail: impossible" }

--------------------------------------------------------------------------------

||| the empty sequence
empty : Seq a
empty = Empty

||| conversion from list, O(n)
export 
fromList : List a -> Seq a
fromList = foldr cons Empty

toList1 : Seq1 n a -> List a
toList1 Nil1             = Nil
toList1 (Skip1 _ t rest) = treeToList t ++ toList1 rest

||| conversion to list, O(n)
export
toList : Seq a -> List a
toList Empty = Nil
toList (Start1 _ t     rest) = treeToList t                   ++ toList1 rest 
toList (Start2 _ t1 t2 rest) = treeToList t1 ++ treeToList t2 ++ toList1 rest 

implementation Show a => Show (Seq a) where
  show seq = "fromList " ++ show (toList seq)

--------------------------------------------------------------------------------

||| singleton sequence
singleton : a -> Seq a
singleton x = Start1 0 (Leaf x) Nil1

||| two-element sequence
pair : a -> a -> Seq a
pair x y = Start2 0 (Leaf x) (Leaf y) Nil1

||| three-element sequence
triple : a -> a -> a -> Seq a
triple x y z = Start1 1 (Cherry x y z) Nil1

||| four-element sequence
quad : a -> a -> a -> a -> Seq a
quad x y z w = Start1 0 (Leaf x) (Skip1 0 (Cherry y z w) Nil1)

--------------------------------------------------------------------------------

||| look up an element at the given index, O(log(i))
lookup : Nat -> Seq a -> Maybe a
lookup i Empty             = Nothing
lookup i (Start1 n t seq1) = 
  let m = treeSize n
  in  if i < m then Just (treeIndex i t) else lookup1 (subtract i m) seq1
lookup i (Start2 n t1 t2 seq1) = 
  let m = treeSize n
  in  if i < m 
        then Just (treeIndex i t1)
        else let j = subtract i m 
             in  if j < m
                   then Just (treeIndex j t2)
                   else lookup1 (subtract j m) seq1

||| look up an element at the given index, O(log(i))
unsafeIndex : Seq a -> Nat -> a
unsafeIndex seq i = case lookup i seq of
  Just y  => y
  Nothing => fatal "unsafeIndex: index out of range"

--------------------------------------------------------------------------------

{-
-- naive implementation of `drop`, O(k)
dropNaive : Nat -> Seq a -> Seq a
dropNaive  Z    seq = seq
dropNaive (S k) seq = case unCons seq of
  Nothing       => Empty
  Just (_,tail) => dropNaive k tail
-}

mutual

  ||| drops the first k elements of a sequence, O(log(k))
  drop : Nat -> Seq a -> Seq a
  drop Z  seq                  = seq
  drop d  Empty                = Empty  
  drop d (Start1 n t1    seq1) = dropTree1 d t1    seq1
  drop d (Start2 n t1 t2 seq1) = dropTree2 d t1 t2 seq1

  dropTree1 : {n : Nat} -> Nat -> Tree n a -> Seq1 (S n) a -> Seq a
  dropTree1 {n= Z} d (Leaf x) cont = case d of
    0 => Start1 0 (Leaf x) cont
    1 => fromSeq1 cont
    _ => drop (subtract d 1) $ fromSeq1 cont 

  dropTree1 {n= n@(S n1)}    Z     t cont = Start1 n t cont
  dropTree1 {n= n@(S n1)} d@(S d1) t cont = 
    let m = treeSize n in if d >= m 
      then drop (subtract d m) $ fromSeq1 cont
      else case dismantle t of
        (_,t1,t2) => dropTree2 d1 t1 t2 (skip1 cont)

  dropTree2 : {n : Nat} -> Nat -> Tree n a -> Tree n a -> Seq1 (S n) a -> Seq a
  dropTree2 {n= Z} d (Leaf x) (Leaf y) cont = case d of
    0 => Start2 0 (Leaf x) (Leaf y) cont
    1 => Start1 0          (Leaf y) cont
    2 => fromSeq1 cont
    _ => drop (subtract d 2) $ fromSeq1 cont 

  dropTree2 {n= n@(S n1)}    Z     t1 t2 cont = Start2 n t1 t2 cont
  dropTree2 {n= n@(S n1)} d@(S d1) t1 t2 cont = 
    let m  = treeSize n 
        mm = m + m 
    in if d >= mm 
      then drop (subtract d mm) $ fromSeq1 cont
      else if d >= m
        then dropTree1 (subtract d m) t2 cont
        else case dismantle t1 of
          (_,s1,s2) => dropTree2 d1 s1 s2 (Skip1 0 t2 cont)

--------------------------------------------------------------------------------
-- testing

{-

prop_toList_fromList : Nat -> Bool
prop_toList_fromList n = 
  let list : List Nat 
      list = [1001..1000+n] 
  in  toList (fromList list) == list

prop_indexing : Nat -> Bool
prop_indexing n = 
  let list : List Nat 
      list = [1001..1001+n]
      seq : Seq Nat
      seq = fromList list
  in and $ map (\i => delay (unsafeIndex seq i == 1001+i)) [0..n]

print_drop : Nat -> IO ()
print_drop n = do
  let seq : Seq Nat
      seq = fromList [0..n]
  sequence_ [ printLn (drop i seq) | i <- [0..n+2] ]

-}

--------------------------------------------------------------------------------
