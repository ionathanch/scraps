# Idris Scraps

A collection of random snippets and scraps of Idris (and sometimes Agda or Coq) files.

* Interlude: A package containing additional definitions for convenience, mostly stolen from Haskell's `base` package.
* IncrementalCycles.idr: An implementation of an acyclic directed graph that can incrementally detect cycles as edges are added.
  This could be used to implement a type synthesis algorithm that can handle floating cumulative universes
  (i.e. universes not attached to some Type 0 at the bottom).
* Girard.idr: An "implementation" of Girard's paradox relying on Type: Type.
  As Idris 2 currently does not have cumulative universes yet, type checking this file will *not* terminate!
* Snipe: A partial proof of the problem given [here](https://sympa.inria.fr/sympa/arc/coq-club/2020-10/msg00010.html)
  (and in [this Tweet](https://twitter.com/TaliaRinger/status/1314805118299037696)).
  Snipe.idr uses pattern-matching on Refl, while SnipeJ avoids this using the J eliminator.
* PropExt.idr: A reproduction of the proof in [this](https://doi.org/10.23638/LMCS-16(2:14)2020) paper
  that impredicativity with some form of propositional extensionality yields non-normalization.
  The final `Omega` term will not compute since Idris doesn't have a proof-irrelevant `Prop`.
* Hedberg.idr: A proof of Hedberg's theorem, that types with decidable equality satisfy UIP.
* ZeroOne.idr: A quick proof of 0 ≠ 1.
* StrictPositivity.idr: An adaptation of [this](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/) proof
  that non-strictly positive inductive types with an impredicative universe yields `Void`.
* Sized.agda: An attempt to index inductive types by depth and make it behave like sized types.
  The final expression cannot be solved; with sized types, this is easily done by setting the size index to ω.
* PredExt.agda: A straightforward proof that propositional extensionality follows from predicate extensionality.
* NestedPositivity.v: Showing that if you don't respect nested positivity, you can derive `False` using impredicative `Prop`.
