
-- initial F-algebras specified by the signature (shape) of the 
-- polynomial functor F; and deriving Eq, Show instances for them

module Generic.InitialAlg

import Decidable.Equality

import Data.Fin
import Data.Vect

import Lib.Misc

--------------------------------------------------------------------------------

-- a positive position
public export
data Pos : Type where
  Rec : Pos                    -- recursive position
  Emb : Type -> Pos            -- embedding of types
  -- Fun : Type -> Pos -> Pos     -- this would allows infinite-branching trees

-- the functor associated to a positive position
public export
PosF : Pos -> (Type -> Type)
PosF pos = \rec => case pos of
  Rec     => rec
  Emb t   => t
  -- Fun t p => t -> PosF p rec 

-- a single constructor
public export
record Con where
  constructor MkCon
  name  : String
  nargs : Nat
  args  : Vect nargs Pos

-- the functor associated to a constructor
public export
ConF : Con -> (Type -> Type)
ConF con t = (i : Fin con.nargs) -> PosF (index i con.args) t

-- the signature of a strictly positive functor
public export
record Sig where
  constructor MkSig
  size  : Nat
  cons  : Vect size Con

-- the functor associated to a signature
public export
SigF : Sig -> (Type -> Type)
SigF sig = \t => (j : Fin sig.size ** ConF (index j sig.cons) t)

-- an F-algebra with the F defined by the given signature
public export
Algebra : Sig -> (Type -> Type)
Algebra sig a = SigF sig a -> a

-- the initial F-algebra
public export
data Initial : Sig -> Type where
  Wrap : {sig : Sig} -> SigF sig (Initial sig) -> Initial sig

-- the initial F-algebra is indeed an F-algebra
export
initialAlgebra : {sig : Sig} -> Algebra sig (Initial sig)
initialAlgebra = Wrap

--------------------------------------------------------------------------------
-- to be able to do anything useful with our types, we need to know
-- that all the types appearing in them implement some interface...

-- a proof that the types appearing in a Pos satisfy some constraint
data PosP : (constraint : Type -> Type) -> Pos -> Type where
  RecP :                               PosP constraint  Rec
  EmbP : (a : Type) -> constraint a -> PosP constraint (Emb a)
  -- FunP : {p : Pos} -> (a : Type) -> ((b : Type) -> constraint (a -> b)) -> PosP constraint (Fun a p)

-- a proof that the types appearing in a constructor satisfy some constraint
data ConP : (constraint : Type -> Type) -> (con : Con) -> Type where
  MkConP : ((i : Fin con.nargs) -> PosP constraint (index i con.args)) -> ConP constraint con

-- a proof that the types appearing in a signature satisfy some constraint
data SigP : (constraint : Type -> Type) -> (sig : Sig) -> Type where
  MkSigP : ((j : Fin sig.size) -> ConP constraint (index j sig.cons)) -> SigP constraint sig

--------------------------------------------------------------------------------
-- generic function: counting nodes

countNodes : {sig : Sig} -> Initial sig -> Nat
countNodes {sig} = countSig where

  mutual

    withCon : (con : Con) -> ConF con t -> (i : Fin con.nargs) -> ((p : Pos) -> PosF p t -> a) -> a
    withCon con conf i f = f (index i con.args) (conf i)

    countSig : Initial sig -> Nat
    countSig (Wrap (j ** con)) = S (countCon (index j sig.cons) con) 
  
    countCon : (con : Con) -> ConF con (Initial sig) -> Nat
    countCon con what = sum $ map (\i => withCon con what i countPos) $ Fin.range {len=con.nargs}

    countPos : (pos : Pos) -> PosF pos (Initial sig) -> Nat
    countPos pos what = case pos of
      Emb _ => Z
      Rec   => countSig what
  
--------------------------------------------------------------------------------
-- generic function: Eq instance

deriveEq : {sig : Sig} -> SigP Eq sig -> Eq (Initial sig)
deriveEq (MkSigP sigprf) = MkEq equals notEquals where

  mutual

    withCon : {con : Con} -> ConP Eq con -> ConF con t -> ConF con t -> (i : Fin con.nargs) 
            -> ((p : Pos) -> PosP Eq p -> PosF p t -> PosF p t -> a) -> a
    withCon {con} (MkConP prf) conf1 conf2 i f = f (index i con.args) (prf i) (conf1 i) (conf2 i)

    notEquals : Initial sig -> Initial sig -> Bool
    notEquals x y =  not (equals x y)
  
    equals : Initial sig -> Initial sig -> Bool
    equals (Wrap (j1 ** con1)) (Wrap (j2 ** con2)) = case decEq j1 j2 of
      No  _    => False
      Yes Refl => equalsCon (sigprf j1) con1 con2
  
    equalsCon : {con : Con} -> ConP Eq con -> ConF con (Initial sig) -> ConF con (Initial sig) -> Bool
    equalsCon {con} prf conf1 conf2 
      = and 
      $ map (\i => delay $ withCon {con=con} prf conf1 conf2 i equalsPos) 
      $ Fin.range {len=con.nargs}

    equalsPos : (pos : Pos) -> PosP Eq pos -> PosF pos (Initial sig) -> PosF pos (Initial sig) -> Bool
    equalsPos pos prf what1 what2 = case prf of
      EmbP a impl => (==) @{impl} what1 what2 
      RecP        => equals what1 what2

--------------------------------------------------------------------------------
-- generic function: Show instance

deriveShow : {sig : Sig} -> SigP Show sig -> Show (Initial sig)
deriveShow (MkSigP sigprf) = MkShow show showSig where

  mutual

    show : Initial sig -> String
    show = showSig Open

    withCon : {con : Con} -> ConP Show con -> ConF con t -> (i : Fin con.nargs) -> Prec  
           -> ((p : Pos) -> PosP Show p -> PosF p t -> Prec -> a) -> a
    withCon {con} (MkConP prf) conf i prec f = f (index i con.args) (prf i) (conf i) prec

    showSig : Prec -> Initial sig -> String
    showSig prec (Wrap (j ** con)) = showCon (sigprf j) con prec
  
    showCon : {con : Con} -> ConP Show con -> ConF con (Initial sig) -> Prec -> String
    showCon {con} prf what prec 
      = showParens (prec >= App && con.nargs > 0) 
      $ con.name ++ intercalateLeft " " (toList xs)
      where
        xs : Vect con.nargs String
        xs = map (\i => withCon {con=con} prf what i App showPos) $ Fin.range {len=con.nargs}

    showPos : (pos : Pos) -> PosP Show pos -> PosF pos (Initial sig) -> Prec -> String
    showPos pos prf what p = case prf of
      EmbP a impl => showPrec @{impl} p what
      RecP        => showSig          p what

--------------------------------------------------------------------------------
-- example: Nat

NatSig : Sig
NatSig = MkSig 2 
  [ MkCon "Z" 0 []
  , MkCon "S" 1 [Rec]
  ]

natProof :  SigP constraint NatSig
natProof = MkSigP $ \j => case j of
  FZ    => MkConP $ \i => absurd i
  FS FZ => MkConP $ \i => case i of { FZ => RecP }

N : Type
N = Initial NatSig

z : N
z = Wrap (0 ** \i => absurd i)

s : N -> N
s x = Wrap (1 ** f) where
  f : ConF (MkCon "S" 1 [Rec]) N        -- unfortunately we need an explicit annotation here for some reason...
  f i = case i of { 0 => x }

toN : Nat -> N
toN  Z    = z
toN (S k) = s (toN k)

fromN : N -> Nat
fromN (Wrap (j ** con)) = case j of
  0 => Z
  1 => S (fromN (con 0))

%hint
natEq : Eq N
natEq = deriveEq natProof

%hint
natShow : Show N
natShow = deriveShow natProof

--------------------------------------------------------------------------------
-- example: List

NilCon : Con
NilCon = MkCon "Nil" 0 []

ConsCon : Type -> Con
ConsCon a = MkCon "Cons" 2 [Emb a, Rec]

ListSig : Type -> Sig
ListSig a = MkSig 2 [NilCon, ConsCon a]

listProof : {a : Type} -> constraint a -> SigP constraint (ListSig a)
listProof {a} impl = MkSigP $ \j => case j of
  FZ    => MkConP $ \i => absurd i
  FS FZ => MkConP $ \i => case i of
    FZ    => EmbP a impl
    FS FZ => RecP

L : Type -> Type
L a = Initial (ListSig a)

nil : {a : Type} -> L a
nil = Wrap (0 ** (\i => absurd i))

cons : {a : Type} -> a -> L a -> L a
cons x xs = Wrap (1 ** f) where
  f : ConF (ConsCon a) (L a)
  f i = case i of { 0 => x ; 1 => xs }

toL : {a : Type} -> List a -> L a
toL []      = nil {a=a}
toL (x::xs) = cons x (toL xs) 

fromL : L a -> List a
fromL (Wrap (j ** con)) = case j of
  0 => Nil
  1 => con 0 :: fromL (con 1)

-- %hint tells the compiler that it should look at this as an implementation?
%hint
listEq : {a : Type} -> Eq a -> Eq (L a)
listEq impl = deriveEq (listProof impl)

%hint
listShow : {a : Type} -> Show a -> Show (L a)
listShow impl = deriveShow (listProof impl)

--------------------------------------------------------------------------------
