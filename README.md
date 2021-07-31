# Scraps

A collection of random snippets and scraps of mostly Idris, Agda, and Coq files.

## Idris Proofs and Libraries

* Interlude: A package containing additional definitions for convenience, mostly stolen from Haskell's `base` package.
* IncrementalCycles.idr: An implementation of an acyclic directed graph that can incrementally detect cycles as edges are added.
  This could be used to implement a type synthesis algorithm that can handle floating cumulative universes
  (i.e. universes not attached to some Type 0 at the bottom).
* Girard.idr: An "implementation" of Girard's paradox relying on Type: Type.
  As Idris 2 currently does not have cumulative universes yet, type checking this file will *not* terminate!
* Girard.agda: Another "implementation" of Girard's paradox, but instead of just using the `--type-in-type` flag,
  it uses an impredicative record with unrestricted elimination implemented using rewrite rules.
  Type checking with this implementation does terminate, but with the flag set and the actual record does not.
* IndInd.idr: A demonstration of Idris' inductive–inductive data definitions with a model
  of a simple dependently-typed language with an intrinsically well-formed environment.
* DeBruijn.idr: The same language in IndInd, but with de Bruijn indices.

## Extensionality Principles

* PropExt.idr: A reproduction of the proof in [this](https://doi.org/10.23638/LMCS-16(2:14)2020) paper
  that impredicativity with some form of propositional extensionality yields non-normalization.
  The final `Omega` term will not compute since Idris doesn't have a proof-irrelevant `Prop`.
* PredExt.agda: A straightforward proof that propositional extensionality follows from predicate extensionality.
* FunExt: An attempt at adding function extensionality as a constructor for the equality type.
  This appears to require an additional parametricity property.

## Miscellaneous Proofs

* Snipe: A partial proof of the problem given [here](https://sympa.inria.fr/sympa/arc/coq-club/2020-10/msg00010.html)
  (and in [this Tweet](https://twitter.com/TaliaRinger/status/1314805118299037696)).
  Snipe.idr uses pattern-matching on Refl, while SnipeJ.idr avoids this using the J eliminator.
* Hedberg.idr: A proof of Hedberg's theorem, that types with decidable equality satisfy UIP.
* NatProps.idr: Proof of 0 ≠ 1 and injectivity of the successor constructor for naturals.
* Ordinals.idr: A construction of some large ordinals following [Ordinals in Type Theory](http://www.cse.chalmers.se/~coquand/ordinal.ps).
* StrictPositivity.idr: An adaptation of [this](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/) proof
  that non-strictly positive inductive types with an impredicative universe yields `Void`.
* NestedPositivity.v: Showing that if you don't respect nested positivity, you can derive `False` using impredicative `Prop`.

## Other
* hm.pl: An incomplete Prolog implementation of Hindley-Milner type inference.
