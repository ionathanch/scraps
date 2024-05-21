/-
  A reproduction of the proofs that impredicativity + proof-irrelevance + regularity ⇒ nonnormalization
  from "Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality":
  https://doi.org/10.23638/LMCS-16(2:14)2020
-/

/-
  A "nonnormalizing" chain of definitional equalities hold
  even without an explicit cast operator;
  however, it can be added like in casting to force reduction
  by defining ω h A = cast (h ⊤ A) δ.
-/
namespace castless
def «⊥» : Prop := ∀ A, A

def neg A := A → «⊥»
prefix:90 (priority := 1001) "¬" => neg

def «⊤» := ¬ «⊥»

def «δ» : «⊤» := λ b ↦ b «⊤» b

def «ω» : ¬ ∀ A B, A → B :=
  λ h A ↦ h «⊤» A «δ»

def «Ω» : ¬ ∀ A B, A → B :=
  λ h ↦ «δ» («ω» h)
  -- («ω» h) «⊤» («ω» h)
  -- (h «⊤» «⊤» «δ») («ω» h)    by def of «ω»
  -- «δ» («ω» h)                by proof irrelevance
end castless

/-
  Normally, Ω would simply reduce to ω,
  but if cast ignores the function when
  casting to a definitionally equal type,
  then it could instead reduce directly to δ ω.
-/
namespace casting
def «⊤» : Prop := ∀ A, A → A

def «δ» : «⊤» → «⊤» :=
  λ t ↦ t («⊤» → «⊤») (λ t ↦ t) t

def cast {A B : Prop} (f : A → B) : A → B := f
-- cast {A} {A} _ a ⤳ a

def «ω» : «⊤» := λ _ a ↦ cast (λ _ ↦ a) «δ»

def «Ω» : «⊤» := «δ» «ω»
-- «ω» («⊤» → «⊤») (λ t ↦ t) «ω»
-- cast (λ _ t ↦ t) «δ» «ω»         by def of «ω»
-- «δ» «ω»                          by proof irrelevance
end casting

/-
  This kind of casting behaviour usually only appears for equality
  as a property called *regularity*.
  Here, we require propositional extensionality.
-/
namespace regular
def tautext {A B : Prop} : A → B → A = B :=
  λ a b ↦ propext ⟨λ _ ↦ b, λ _ ↦ a⟩

def «⊤» : Prop := ∀ A, A → A

def «δ» : «⊤» → «⊤» :=
  λ t ↦ t («⊤» → «⊤») (λ t ↦ t) t

def cast {A B : Prop} (p : A = B) : A → B := by simp [p]
-- cast {A} {A} _ a ⤳ a

def «ω» : «⊤» := λ _ a ↦ cast (tautext (λ x ↦ x) a) «δ»

def «Ω» : «⊤» := «δ» «ω»
-- «ω» («⊤» → «⊤») (λ t ↦ t) «ω»
-- cast (tautext (λ x ↦ x) (λ t ↦ t)) «δ» «ω»    by def of «ω»
-- «δ» «ω»                                       by regularity
end regular
