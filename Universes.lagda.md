# Modelling Universes with Induction–Recursion

Providing a model for a type universe is easy and free.
`U` is a set of codes for types;
`el` decodes the codes into Agda types.

```agda
data ⊥ : Set where

module ez where
  data U : Set
  el : U → Set

  data U where
    Bottom : U
    Pi : (A : U) → (el A → U) → U

  el Bottom = ⊥
  el (Pi A B) = (a : el A) → el (B a)
```

## A Universe Hierarchy

Providing one for many universes is not so easy.
Each universe needs a code, and every code needs an interpretation.
How do we model a hierarchy of universes without necessarily interpreting them as universes in the theory?
Luckily, we can follow [Kovács (2021)](https://arxiv.org/abs/2103.00223)
and parametrize `U` by universe levels.
First, we require that levels be well founded with respect to some strict order,
using the usual accessibility predicate,
as well as proof irrelevance of that predicate,
which is provable by assuming function extensionality.

```agda
open import Relation.Binary.PropositionalEquality

module _ (Level : Set)
         (_<_ : Level → Level → Set)
         (trans< : ∀ {i j k} → i < j → j < k → i < k) where

  data Acc k : Set where
    acc : (∀ {j} → j < k → Acc j) → Acc k

  postulate
    funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

  AccIsProp : ∀ {k} (p q : Acc k) → p ≡ q
  AccIsProp (acc p) (acc q) = cong (λ pq → acc (λ {j} j<k → pq j j<k))
    (funext (λ j → funext (λ j<k → AccIsProp (p {j} j<k) (q {j} j<k))))
```

To sidestep strict positivity issues,
`U k` and `el k` are parametrized by some `∀ j → j < k → Set`
that returns the interpretation of a smaller code,
which we'll fill in later.

```agda
  module Kovács (wf : ∀ k → Acc k) where
    data U' k (f : ∀ {j} → j < k → Set) : Set
    el' : ∀ {k} {f : ∀ {j} → j < k → Set} → U' k f → Set

    data U' k f where
      Û : ∀ {j} → j < k → U' k f
      Bottom : U' k f
      Pi : (A : U' k f) → (el' A → U' k f) → U' k f

    el' {f = f} (Û j<k) = f j<k
    el' Bottom = ⊥
    el' (Pi A B) = (a : el' A) → el' (B a)
```

The real `U` is then defined by induction over accessibility of the levels,
which is what allows `f` to return `U'`s as the interpretations of their codes.

```agda
    U< : ∀ {k} → Acc k → ∀ {j} → j < k → Set
    U< {k} (acc p) {j} j<k = U' j (U< (p j<k))

    U : ∀ k → Set
    U k = U' k (U< (wf k))

    el : ∀ {k} → U k → Set
    el {k} = el' {f = U< (wf k)}
```

We would like to ensure two properties:

* The sets of codes `U` are cumulative with respect to the levels; and
* The interpretations of the same codes across different levels are the same.

These need to be proven mutually due to the induction–recursion.

```agda
    lift : ∀ {j k} → j < k → U j → U k
    el≡ : ∀ {j k} (j<k : j < k) (u : U j) → el u ≡ el (lift j<k u)

    lift j<k (Û i<j) = Û (trans< i<j j<k)
    lift j<k Bottom = Bottom
    lift j<k (Pi A B) rewrite (el≡ j<k A) = Pi (lift j<k A) (λ a → lift j<k (B a))

    el≡ {j} {k} j<k (Û i<j) with wf j | wf k
    ... | acc p | acc q = cong (λ acc → U' _ (U< acc)) (AccIsProp (p i<j) (q (trans< i<j j<k)))
    el≡ j<k Bottom = refl
    el≡ j<k (Pi A B) rewrite (el≡ j<k A) = cong (λ b → (a : el (lift j<k A)) → b a) p where
      p : (λ a → el (B a)) ≡ (λ a → el (lift j<k (B a)))
      p = funext (λ a → el≡ j<k (B a))
```

## Another Universe Hierarchy

But that's very hard to think about.
There's an indirection through accessibility of the levels,
and reasoning about how `el` behaves requires mentally matching and unfolding many of these accessibility predicates.
Conceptually, though, it's very reasonable:
we're defining, by induction on the levels,
a separate inductive–recursive definition,
where we decode smaller codes into smaller `U`s.
This construction is valid,
since by the time `el` decodes a code of a smaller `U`,
it's available to us by the induction hypothesis on the levels,
and resembles that by [Gratzer (2022)](https://arxiv.org/abs/2202.05529).
We can't define this in Agda,
since there are no inductive–(inductive–recursive) definitions
(not to be confused with (inductive–inductive)–recursive definitions),
and even defining a single level will cause Agda to complain about strict positivity,
but we can turn that off on the basis that Agda is a machine and we are type theorists.

```agda
  module Gratzer (wf : ∀ k → Acc k) where
    data U k : Set
    el : ∀ {k} → U k → Set

    {-# NO_POSITIVITY_CHECK #-}
    data U k where
      Û : ∀ {j} → j < k → U k
      Bottom : U k
      Pi : (A : U k) → (el A → U k) → U k
    
    el (Û {j} j<k) = U j
    el Bottom = ⊥
    el (Pi A B) = (a : el A) → el (B a)
```

This is much simpler to conceptualize,
and proving the two properties of `U` and `el` no longer requires reasoning about accessibility.

```agda
    lift : ∀ {j k} → j < k → U j → U k
    el≡ : ∀ {j k} (j<k : j < k) (u : U j) → el u ≡ el (lift j<k u)

    lift j<k (Û i<j) = Û (trans< i<j j<k)
    lift j<k Bottom = Bottom
    lift j<k (Pi A B) rewrite (el≡ j<k A) = Pi (lift j<k A) (λ a → lift j<k (B a))

    el≡ {j} {k} j<k (Û i<j) = refl
    el≡ j<k Bottom = refl
    el≡ j<k (Pi A B) rewrite (el≡ j<k A) = cong (λ b → (a : el (lift j<k A)) → b a) p where
      p : (λ a → el (B a)) ≡ (λ a → el (lift j<k (B a)))
      p = funext (λ a → el≡ j<k (B a))
```

## Type in Type is Fine

The Gratzer model works because we assume by induction that `U` and `el` are fully defined for smaller levels,
and because in `el k`, we never ever ever return `U k`, which is *not* yet fully defined.
What if we instead never ever ever *call* `el k` when defining `U k`,
and only ever use `el j` for strictly smaller `j`?
We are then defining, by induction over levels,
first `U k` in its entirety, then `el k` in its entirety,
where we are free to use `U j` and `el j` for strictly smaller `j`.
Rather than an inductive–(inductive–recursive) definition,
this is more like an inductive–(inductive+recursive) definition.

Interestingly, because `el k` is now free to use `U k`,
it can decode a code for `U k`,
which means we are permitted to include the code for `U k` *in itself*.
The key to consistency is that no interpretation of a code in `U k` ever *uses* `U k` itself.
Again, we define this with strict positivity turned off,
which is justified by the same reasoning behind the Gratzer model.

```agda
  data _≤_ : Level → Level → Set where
    eq : ∀ {k} → k ≤ k
    lt : ∀ {j k} → j < k → j ≤ k

  module TypeInType (wf : ∀ k → Acc k) where
    data U k : Set
    el : ∀ {k} → U k → Set

    {-# NO_POSITIVITY_CHECK #-}
    data U k where
      Û : ∀ {j} → j ≤ k → U k
      Bottom : U k
      Pi : ∀ {j} → j < k → (A : U j) → (el A → U k) → U k
    
    el (Û {j} j≤k) = U j
    el Bottom = ⊥
    el (Pi j<k A B) = (a : el A) → el (B a)
```

To restrict uses of `el` in `U k` to only on `j`,
codes of function types must now only quantify over codes in a strictly smaller universe.
`el k` may return `U k`, but never to the left of an arrow in `Pi`.
We have merely moved the strict inequality from the definition of `el` to the definition of `Pi`;
there is no trickery here.
Finally, we prove `lift` and `eq≡` as usual, this time separately,
since `U` and `el` are no longer inductive–recursive.

```agda
    lift : ∀ {j k} → j < k → U j → U k
    lift j<k (Û eq) = Û (lt j<k)
    lift j<k (Û (lt i<j)) = Û (lt (trans< i<j j<k))
    lift j<k Bottom = Bottom
    lift j<k (Pi i<j A B) = Pi (trans< i<j j<k) A (λ a → lift j<k (B a))

    el≡ : ∀ {j k} (j<k : j < k) (u : U j) → el u ≡ el (lift j<k u)
    el≡ j<k (Û eq) = refl
    el≡ j<k (Û (lt i<j)) = refl
    el≡ j<k Bottom = refl
    el≡ j<k (Pi i<j A B) = cong (λ b → (a : el A) → b a) p where
      p : (λ a → el (B a)) ≡ (λ a → el (lift j<k (B a)))
      p = funext (λ a → el≡ j<k (B a))
```

## Once Again with Accessibility

It turns out it is possible to define the type-in-type model via accessibility of levels
using the same trick in Kovács' model,
but instead of parametrizing `U'` and `el'` over only smaller instances of `U'`,
we parametrize them over smaller instances of both `U'` and `el'`.
They are then used in the domain of function types,
which belong to a smaller universe.

```agda
  module TypeInTypeAcc (wf : ∀ k → Acc k) where
    data U' k (U<  : ∀ {j} → j < k → Set)
              (el< : ∀ {j} → (j<k : j < k) → U< j<k → Set) : Set where
      Û : ∀ {j} → j ≤ k → U' k U< el<
      Bottom : U' k U< el<
      Pi : ∀ {j} → (j<k : j < k) → (A : U< j<k) → (el< j<k A → U' k U< el<) → U' k U< el<

    el' : ∀ {k} (U<  : ∀ {j} → j < k → Set)
                (el< : ∀ {j} → (j<k : j < k) → U< j<k → Set) →
          U' k U< el< → Set
    el' U< el< (Û {k} eq) = U' k U< el<
    el' U< el< (Û {j} (lt j<k)) = U' j (λ i<j → U< (trans< i<j j<k)) (λ i<j → el< (trans< i<j j<k))
    el' _ _ Bottom = ⊥
    el' U< el< (Pi j<k A B) = (a : el< j<k A) → (el' U< el< (B a))
```

Once again, we define `U<` and `el<` by mutual induction over accessibility,
then tie the knot with well-foundedness of the levels.

```agda
    U<  : ∀ {k} → Acc k → ∀ {j} → j < k → Set
    el< : ∀ {k} (p : Acc k) {j} (j<k : j < k) → U< p j<k → Set

    U<  (acc f) {j} j<k = U' j (U< (f j<k)) (el< (f j<k))
    el< (acc f) {j} j<k = el'  (U< (f j<k)) (el< (f j<k))

    U : ∀ k → Set
    U k = U' k (U< (wf k)) (el< (wf k))

    el : ∀ {k} → U k → Set
    el {k} = el' (U< (wf k)) (el< (wf k))
```

Defining lifting from smaller universes to larger universes directly is difficult.
Instead, we lift `U'`, generalizing over all accessibility predicates involved
so that applying `AccIsProp` is simpler,
then instantiate with `wf` as needed.

```agda
    lift' : ∀ {j k} {accj : Acc j} {acck : Acc k} → j < k →
      U' j (U< accj) (el< accj) → U' k (U< acck) (el< acck)
    lift' j<k (Û {k} eq) = Û (lt j<k)
    lift' j<k (Û {i} (lt i<j)) = Û (lt (trans< i<j j<k))
    lift' _ Bottom = Bottom
    lift' {_} {_} {acc f} {acc g} j<k (Pi i<j A B)
      rewrite AccIsProp (f i<j) (g (trans< i<j j<k)) =
      Pi (trans< i<j j<k) A (λ a → lift' j<k (B a))

    lift : ∀ {j k} → j < k → U j → U k
    lift = lift'
```

Unfortunately, proving `el≡` is much more complicated.
We can generalize over all accessibility predicates as above.

```agda
    el≡' : ∀ {j k} {accj : Acc j} {acck : Acc k} (j<k : j < k) (u : U' j (U< accj) (el< accj)) →
      el' (U< accj) (el< accj) u ≡ el' (U< acck) (el< acck) (lift' j<k u)
    el≡' {j} {k} {acc f} {acc g} j<k (Û eq) = {!   !}
    el≡' {_} {_} {acc f} {acc g} j<k (Û (lt i<j)) = {!   !}
    el≡' j<k Bottom = refl
    el≡' {_} {_} {acc f} {acc g} j<k (Pi i<j A B) = {!   !}

    el≡ : ∀ {j k} (j<k : j < k) (u : U j) → el u ≡ el (lift j<k u)
    el≡ = el≡'
```

Where the holes remain, things start to get hairy.
The first hole, for instance, requires that we show that

```haskell
U' j (λ {i} i<j → U' i (U< (f i<j)) (el< (f i<j)))
     (λ {i} i<j → el'  (U< (f i<j)) (el< (f i<j))) ≡
U' j (λ {i} i<j → U' i (U< (g (trans< i<j j<k))) (el< (g (trans< i<j j<k))))
     (λ {i} i<j → el'  (U< (g (trans< i<j j<k))) (el< (g (trans< i<j j<k))))
```

which, while true, requires a ton of applications of `cong` over `funext` and `AccIsProp`.
And that's only the simplest case,
with the final hole likely being the most complex,
so for now I leave them as holes.