# Mendler Encodings of Inductive Data in Cedille

* `Mendler.ced`: Reproduction of code in *Efficient Mendler-Style Lambda-Encodings in Cedille*
  [[arXiv](https://arxiv.org/abs/1803.02473); [DOI](https://doi.org/10.1007/978-3-319-94821-8_14); [SpringerLink](https://link.springer.com/chapter/10.1007%2F978-3-319-94821-8_14)].
  Encodes inductive datatypes as functors that only have identity mappings,
  with a weak structural induction principle.
* `MendlerCV.ced`: Reproduction of code in *Course-of-Values Induction in Cedille*
  [[arXiv](https://arxiv.org/abs/1811.11961); [abstract](http://firsov.ee/cov-induction/)].
  Encodes the same as above but with a course-of-values induction (i.e. strong structural induction) principle.
* `Large.ced`: Reproduction of code in *Simulating Large Eliminations in Cedille*
  [[arXiv](https://arxiv.org/abs/2112.07817)].
  Shows that relational folds of type algebras uniquely exist and are respectful wrt type equality.
* `Utils.ced`: Utilities for the above — dependent pairs and identity mappings.
  Yes, dependent pairs are implemented using Cedille's data mechanism,
  which is what I'm trying to reproduce; this is just for convenience.
  The `Id` type is called `Cast` in Cedille's library and in later papers,
  because an identity mapping between two types is a zero-cost type cast.

## Category-Theoretical Concepts

As it turns out, there's no need to understand any of these mean (except maybe for how identity mappings are implemented) to just follow the types.
* `Mendler.ced`: functors, identity mappings<sup>†</sup>, natural transformations, F-algebras, Q-proof F-algebras, folds (catamorphisms?), Lambek's lemma
* `MendlerCV.ced` (in addition to the above): difunctors, dinatural transformations, (H-restricted) F-coends, (H-restricted) F-cowedges

<sup>†</sup> Do functors without compositionality have their own name? Monotonic type morphisms?
