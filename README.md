
Experiments with dependently-typed programming in Idris2
--------------------------------------------------------

This repo contains various small-to-medium sized experiments
in dependently typed programming. For example:

* `Small.Printf`: type-safe `printf`
* `Small.Fix`: n-ary (or multi-kinded) fixpoint type
* `Data.RAL`: skew-binary random access lists (using dependent types internally)
* `Lambda.STLC`: well-typed interpreter for simply typed lambda calculus
* `Parsing.JSON`: JSON parsing into a schema-indexed JSON type (inference and validation)
* `SQL.*`: type-safe implementation of a query language similar to SQL (work in progress)
* `Generic.NonRecursive`: generic parsing / pretty-printing of (non-recursive) algebraic datatypes
* `Generic.InitialAlg`: initial algebras of polynomial functors + generic `Eq` / `Show`

Other possible exercises:

* insertion sort with proof of correctness
* tensor algebra
* generic programming:
    * generic data structures (for example generic tries)
    * modelling recursive, maybe indexed algebraic datatypes 
    * generic programming for trees
* modelling some subset of the commutative algebra hierarchy?
* type-safe (dependent) protocol descriptions
* modelling optics
* implementing an effect system
* regexp parser
* mixfix parser (into mutually recursive AST-s)
* ...
