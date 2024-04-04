# Scraps

A collection of random snippets and scraps of mostly Idris, Agda, and Rocq files.

## Extensionality Principles

* PropExt.idr: A reproduction of the proof in [this paper](https://doi.org/10.23638/LMCS-16(2:14)2020)
  that impredicativity with some form of propositional extensionality yields non-normalization.
  The final `Omega` term will not compute since Idris doesn't have a proof-irrelevant `Prop`.
* PropImpred.agda: Another reproduction of the proofs in the above,
  but without using any notion of equality explicitly.
* PredExt.agda: A straightforward proof that propositional extensionality follows from predicate extensionality.
* FunExt: An attempt at adding function extensionality as a constructor for the equality type.
  This appears to require an additional parametricity property.
* untyped-reflect.tex: A LaTeX derivation of falsehood when combining equality reflection with
  untyped conversion that supports congruence and transitivity.

## Inconsistencies

* Hurkens.idr: An "implementation" of Hurkens' paradox relying on Type: Type.
  As Idris 2 currently does not have cumulative universes yet, type checking this file will *not* terminate!
* HurkensLower.agda: Another "implementation" of Hurkens' paradox, but instead of just using the `--type-in-type` flag,
  it uses an impredicative record with unrestricted elimination implemented using rewrite rules.
  Type checking with this implementation does terminate, but with the flag set and the actual record does not.
* Hurkens.agda, Hurkens.v: Yet another "implementation" of Hurkens' paradox,
  using universe polymorphism to try to get it to type check as far as possible.
* Berardi.agda: An adaptation of the inconsistency arising from impredicativity, AoC, and EM from
  [Proof-irrelevance out of excluded-middle and choice in the calculus of constructions](https://doi.org/10.1017/S0956796800001829).
* StrictPositivity.idr: An adaptation of [this proof](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/)
  that non-strictly positive inductive types with an impredicative universe yields `Void`.
* StrictPositivity.agda: Same thing as above but in Agda.
* StrictPositivity.v: Same thing as above but in Rocq.
* NestedPositivity.v: Showing that if you don't respect nested positivity, you can derive `False` using impredicative `Prop`.
* SizedFalse.agda: A few short proofs of false using sized types.
* CoquandGirard.agda: Abandoned attempt at mechanizing Girard's original paradox as described by Coquand.
* WFU.agda, WFU.v: Coquand's Paradox of Trees, an inductive flavour of Burali-Forti's paradox.

## Propositional Equality

* Snipe: A partial proof of the problem given [here](https://sympa.inria.fr/sympa/arc/coq-club/2020-10/msg00010.html)
  (and in [this Tweet](https://twitter.com/TaliaRinger/status/1314805118299037696)).
  Snipe.idr uses pattern-matching on Refl, while SnipeJ.idr avoids this using the J eliminator.
* Hedberg.idr: A proof of Hedberg's theorem, that types with decidable equality satisfy UIP.
* Hedberg.agda: Two proofs of Hedberg's theorem, one via a reflexive mere relation implying equality
  and another via a constant endofunction on equalities (path collapsibility).
* Equality.agda: Implementing propositional equality from scratch using rewrite rules 
  (see [Notes on Propositional Equality](https://ionathan.ch/2021/05/25/notes-on-equality.html)).
* DIP.ced: Demonstration that Cedille refutes UIP due to the Kleene trick.
* ObsEq.agda: An attempt at encoding observational equality à la Tarski as recursion over codes.

## Guarded Types and Coinduction
* Guardedness.agda: Some examples of coprograms that don't pass productivity checking.
* Guarded.agda: Some examples using Agda's Guarded Type Theory support.
* Clocked.agda: Coinductive types à la Clocked Type Theory via Agda's support for guarded types,
  using a postulated forcing tick which Agda doesn't like :(

## Programs

* Interlude: A package containing additional definitions for convenience, mostly stolen from Haskell's `base` package.
* IncrementalCycles.idr: An implementation of an acyclic directed graph that can incrementally detect cycles as edges are added.
  This could be used to implement a type synthesis algorithm that can handle floating cumulative universes
  (i.e. universes not attached to some Type 0 at the bottom).
* Fib.agda: The nth Fibonacci number via instance search of a data type encoding the recursive structure of computing them
  (for @braxtonhall).
* TTT.rkt: A simple type theory that's a little more than CoC... but not by much.
* cedille.rkt: An abandoned Redex model of Cedille that never made it past syntax.
* hm.pl: An incomplete Prolog implementation of Hindley-Milner type inference.

## Models
* IndInd.idr: A demonstration of Idris' inductive–inductive data definitions with a model
  of a simple dependently-typed language with an intrinsically well-formed environment.
* IndInd.agda: An attempt at encoding an inductive–inductive type in Agda as a mutual indexed type;
  there appears to be a problem with the elimination principle.
  (See [Constructing Inductive-Inductive Types via Type Erasure](https://eutypes.cs.ru.nl/eutypes_pmwiki/uploads/Main/books-of-abstracts-TYPES2019.pdf#page=20).)
* DeBruijn.idr: The same language in IndInd, but with de Bruijn indices.
* IndRec.agda: Inductive–recursive data definitions in practice with the Kipling embedding
  from [Outrageous but Meaningful Coincidences](https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf).
* CwF.agda, CwFModel.agda: A definition of a category with families in Agda, complete with equalities that must be satisfied,
  and a model using induction--recursion to define type encodings.
* Universes.lagda.md: Various ways to model a universe hierarchy.
* StraTT.agda: A model of the universes of stratified type theory with explicit universe levels.
  The actual structures for the types are excluded because working with accessibility predicates is too messy.
* SystemF.agda: A reproduction of the model (i.e. interpreter) of Stratified System F from
  [Towards Tagless Interpretation of System F](https://icfp23.sigplan.org/details/tyde-2023/12/),
  extended with a parametricity theorem.

## Miscellaneous Proofs

* NatProps.idr: Proof of 0 ≠ 1 and injectivity of the successor constructor for naturals.
* Ordinals.idr: A construction of some large ordinals following [Ordinals in Type Theory](http://www.cse.chalmers.se/~coquand/ordinal.ps).
* Ordinals.ced: The generalization of ordinal trees in an impredicative setting is not well-founded.
* Ordinals.agda: As above, but with an explicit proof of falsehood.
* Sized.agda: Examples of sized types used in [How to Use Sized Types? Let Me Count the Ways](https://ionathan.ch/2021/08/26/using-sized-types.html).
* Acc.agda: An attempt at formalizing the quicksort example from [this Tweet](https://twitter.com/jonmsterling/status/1444640259552251921)
  originally found in [Modelling General Recursion in Type Theory](http://dx.doi.org/10.1017/S0960129505004822) but failed at Step 3.
* GenericOrd.agda: An attempt at defining some sort of type-level `Ord` using [Practical Generic Programming](https://jesper.sikanda.be/files/practical-generic-programming.pdf).
* Cedille.ced: A cheat sheet for Cedille; see the [wiki page](https://github.com/ionathanch/ionathanch/wiki/Cedille).
* CastTpEq.ced: The Cast and TpEq constructs used in various Cedille developments, also found in the [core library](https://github.com/cedille/cedille/tree/master/new-lib/core).
* Mendler: Mendler-style encodings of (weak, strong) induction in Cedille.
* Injectivity.ced: An old attempt at proving injectivity of constructors in Cedille.
