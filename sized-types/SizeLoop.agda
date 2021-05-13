{-
  A counterexample from Section 5.1 of Andreas Abel's dissertation [1],
  showing that the types of recursive functions must be (semi-)continuous,
  i.e. `loop` below should be disallowed.
  In the example, `loop` is not used as-is, but rather the size involved
  is instantiated to the infinite size in order to pass in `plus2`.

  The conditions on ω-instantiating from John Hughes' paper [2] is
  essentially a stricter condition than Abel's semi-continuity on where
  size variables may appear in the type.

  [1] A Polymorphic Lambda-Calculus with Sized Higher-Order Types
  [2] Proving the Correctness of Reactive Systems using Sized Types
-}

data Size : Set where
  ∘ : Size
  ↑_ : Size → Size

data Nat : Size → Set where
  zero : ∀ {s} → Nat (↑ s)
  succ : ∀ {s} → Nat s → Nat (↑ s)

data NatInf : Set where
  ⟦_⟧ : ∀ {s} → Nat s → NatInf

zero∘ : Nat (↑ ∘)
zero∘ = zero {∘}

shift : ∀ {s} → (NatInf → Nat (↑ (↑ s))) → NatInf → Nat (↑ s)
shift f ⟦ n ⟧ with f ⟦ succ n ⟧
... | zero = zero
... | succ m = m

plus2 : NatInf → NatInf
plus2 ⟦ n ⟧ = ⟦ succ (succ n) ⟧

loop : ∀ {s} → Nat s → (NatInf → Nat (↑ s)) → NatInf
loop _ f with f ⟦ zero∘ ⟧
... | zero          = ⟦ zero∘ ⟧
... | succ zero     = ⟦ zero∘ ⟧
... | succ (succ k) = loop k (shift f)

{- 
  Interpreting Nat^∞ as a size-paired natural, we need to somehow
  derive an infinity-instantiated version (`loopInf`) using `loop`,
  but we cannot produce a `NatInf → Nat (↑ s)` out of `NatInf → NatInf`:
  doing so amounts to proving `∃s. Nat s → ∀s. Nat s`.
-}

-- loop cannot be instantiated with an infinite size
postulate loopInf : NatInf → (NatInf → NatInf) → NatInf

uhoh : NatInf
uhoh = loopInf ⟦ zero∘ ⟧ plus2
