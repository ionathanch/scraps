# Scraps

A collection of random snippets and scraps of mostly Idris, Agda, and Coq files.

## Extensionality Principles

* PropExt.idr: A reproduction of the proof in [this paper](https://doi.org/10.23638/LMCS-16(2:14)2020)
  that impredicativity with some form of propositional extensionality yields non-normalization.
  The final `Omega` term will not compute since Idris doesn't have a proof-irrelevant `Prop`.
* PredExt.agda: A straightforward proof that propositional extensionality follows from predicate extensionality.
* FunExt: An attempt at adding function extensionality as a constructor for the equality type.
  This appears to require an additional parametricity property.

## Inconsistencies

* Girard.idr: An "implementation" of Girard's paradox relying on Type: Type.
  As Idris 2 currently does not have cumulative universes yet, type checking this file will *not* terminate!
* Girard.agda: Another "implementation" of Girard's paradox, but instead of just using the `--type-in-type` flag,
  it uses an impredicative record with unrestricted elimination implemented using rewrite rules.
  Type checking with this implementation does terminate, but with the flag set and the actual record does not.
* Berardi.agda: An adaptation of the inconsistency arising from impredicativity, AoC, and EM from
  [Proof-irrelevance out of excluded-middle and choice in the calculus of constructions](https://doi.org/10.1017/S0956796800001829).
* StrictPositivity.idr: An adaptation of [this proof](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/)
  that non-strictly positive inductive types with an impredicative universe yields `Void`.
* StrictPositivity.agda: Same thing as above but in Agda.
* NestedPositivity.v: Showing that if you don't respect nested positivity, you can derive `False` using impredicative `Prop`.

## Propositional Equality

* Snipe: A partial proof of the problem given [here](https://sympa.inria.fr/sympa/arc/coq-club/2020-10/msg00010.html)
  (and in [this Tweet](https://twitter.com/TaliaRinger/status/1314805118299037696)).
  Snipe.idr uses pattern-matching on Refl, while SnipeJ.idr avoids this using the J eliminator.
* Hedberg.idr: A proof of Hedberg's theorem, that types with decidable equality satisfy UIP.
* Hedberg.agda: Two proofs of Hedberg's theorem, one via a reflexive mere relation implying equality
  and another via a constant endofunction on equalities (path collapsibility).
* Equality.agda: Implementing propositional equality from scratch using rewrite rules 
  (see [Notes on Propositional Equality](https://ionathan.ch/2021/05/25/notes-on-equality.html)).

## Programs

* Interlude: A package containing additional definitions for convenience, mostly stolen from Haskell's `base` package.
* IncrementalCycles.idr: An implementation of an acyclic directed graph that can incrementally detect cycles as edges are added.
  This could be used to implement a type synthesis algorithm that can handle floating cumulative universes
  (i.e. universes not attached to some Type 0 at the bottom).
* hm.pl: An incomplete Prolog implementation of Hindley-Milner type inference.

## Miscellaneous Proofs

* IndInd.idr: A demonstration of Idris' inductive–inductive data definitions with a model
  of a simple dependently-typed language with an intrinsically well-formed environment.
* IndRec.agda: Inductive–recursive data definitions in practice with the Kipling embedding
  from [Outrageous but Meaningful Coincidences](https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf).
* DeBruijn.idr: The same language in IndInd, but with de Bruijn indices.
* NatProps.idr: Proof of 0 ≠ 1 and injectivity of the successor constructor for naturals.
* Ordinals.idr: A construction of some large ordinals following [Ordinals in Type Theory](http://www.cse.chalmers.se/~coquand/ordinal.ps).
* Sized.agda: Examples of sized types used in [How to Use Sized Types? Let Me Count the Ways](https://ionathan.ch/2021/08/26/using-sized-types.html).
* Acc.agda: An attempt at formalizing the quicksort example from [this Tweet](https://twitter.com/jonmsterling/status/1444640259552251921)
  originally found in [Modelling General Recursion in Type Theory](http://dx.doi.org/10.1017/S0960129505004822) but failed at Step 3.
* Cedille.ced: A cheat sheet for Cedille; see the [wiki page](https://github.com/ionathanch/ionathanch/wiki/Cedille).
* CastTpEq.ced: The Cast and TpEq constructs used in various Cedille developments, also found in the [core library](https://github.com/cedille/cedille/tree/master/new-lib/core).
