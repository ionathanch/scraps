# Models of ECC

This repository contains various different ways of modelling Luo's Extended Calculus of Constructions, usually with a few additions:

* Local definitions (let expressions), with or without type annotations
* Booleans with dependent conditionals (elimination)
* Polymorphic universes (Redex only)

## Beluga

Beluga is an LF-like proof assistant using contextual type theory to implement higher-order abstract syntax. An installation guide can be found [here](https://github.com/Beluga-lang/Beluga/blob/master/INSTALL), and a reference manual [here](http://complogic.cs.mcgill.ca/beluga/userguide2/userguide.pdf).

The Beluga model has reduction, conversion, equivalence, subtyping, and typing relations. An attempt at proving subject reduction was made.

## Redex

Redex is a Racket library for modelling languages with binding, reduction relations, and judgements. The reference can be found [here](https://docs.racket-lang.org/redex/The_Redex_Reference.html).

The Redex model implements type synthesis for ECC with universe polymorphism and anonymous universes using an algorithm from Type Checking with Universes. The constraint-checker is incredibly inefficient and not yet actually used in the type synthesis algorithm. The paper doesn't specify how relationships between concrete type levels (i.e. naturals) should be enforced, so at the moment, for every pair of naturals (i, j), if (i < j), then we add this edge to the graph. Much testing remains to be done.

## Idris

Idris is a general-purpose dependently-typed language based on quantitative type theory, with support for writing proofs. This repo uses Idris 2, whose documentation can be found [here](https://idris2.readthedocs.io/en/latest/app/index.html). The [Idris 1 documentation](http://docs.idris-lang.org/en/latest/index.html) is helpful as well. The installation guide for Idris 2 is [here](https://github.com/edwinb/Idris2/blob/master/INSTALL.md).

The Idris model implements variables using a locally-nameless shifted-names scope-safe representation. That is, bound variables are implemented using de Bruijn levels, the levels are never greater than the binding depth, and free variables are implemented using names with indices to avoid collision. The shifted-names implementation is complete, but lacks proofs of all its properties, which may be translated from the [Coq implementation](https://github.com/lpw25/shifted-names) at some point.

There are a few other Idris files unrelated to ECC:
* IncrementalCycles: An implementation of an acyclic directed graph that can incrementally detect cycles as edges are added. This could be used to implement a type synthesis algorithm that can handle floating cumulative universes (i.e. universes not attached to some Type 0 at the bottom).
* Girard: An "implementation" of Girard's paradox relying on Type: Type. As Idris 2 currently does not have cumulative universes yet, type checking this file will *not* terminate!
* Interlude: A package containing additional definitions for convenience, mostly stolen from Haskell's `base` package.
* EqIso: A collection of properties and proofs about equalities and isomorphisms. This may be put into Interlude later.
