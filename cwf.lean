set_option autoImplicit false
set_option pp.fieldNotation false

section
set_option hygiene false
local infix:40 "⟹" => hom
local infix:70 "∘" => comp
local notation:50 "•" => I
local notation:60 A:61 "[" σ:61 "]" => substTy A σ
local notation:60 a:61 "[" σ:61 "]" => substTm a σ
local notation:50 Γ:51 "▷" A:51 => cons Γ A
local notation:80 "⟪" γ:81 "," a:81 "⟫" => comm γ a
local infix:70 "↑" => consHom

class CwF where
  𝒞 : Type
  hom : 𝒞 → 𝒞 → Type
  id {Γ} : Γ ⟹ Γ
  comp {Ξ Δ Γ} : Δ ⟹ Γ → Ξ ⟹ Δ → Ξ ⟹ Γ
  I : 𝒞
  ε {Γ} : Γ ⟹ •

  assoc {Θ Ξ Δ Γ} (σ : Δ ⟹ Γ) (τ : Ξ ⟹ Δ) (υ : Θ ⟹ Ξ) : (σ ∘ τ) ∘ υ = σ ∘ (τ ∘ υ)
  idₗ {Δ Γ} (σ : Δ ⟹ Γ) : id ∘ σ = σ
  idᵣ {Δ Γ} (σ : Δ ⟹ Γ) : σ ∘ id = σ
  εη {Γ} (σ : Γ ⟹ •) : σ = ε

  L : Type
  Ty : L → 𝒞 → Type
  Tm k Γ : Ty k Γ → Type
  substTy {k Δ Γ} : Ty k Γ → Δ ⟹ Γ → Ty k Δ
  substTm {k Δ Γ} {A : Ty k Γ} : Tm k Γ A → (σ : Δ ⟹ Γ) → Tm k Δ (A [ σ ])

  substTyId {k Γ} {A : Ty k Γ} : A [ id ] = A
  substTmId {k Γ} {A : Ty k Γ} {a : Tm k Γ A} : a [ id ] = (by rw [substTyId]; exact a)
  substTyComp {k Ξ Δ Γ} {σ : Δ ⟹ Γ} {τ : Ξ ⟹ Δ} {A : Ty k Γ} : A [ σ ∘ τ ] = (A [ σ ]) [ τ ]
  substTmComp {k Ξ Δ Γ} {σ : Δ ⟹ Γ} {τ : Ξ ⟹ Δ} {A : Ty k Γ} {a : Tm k Γ A} :
    a [ σ ∘ τ ] = (by rw [substTyComp]; exact (a [ σ ]) [ τ ])

  cons {k} Γ : Ty k Γ → 𝒞
  comm {k Δ Γ} {A : Ty k Γ} (σ : Δ ⟹ Γ) : Tm k Δ (A [ σ ]) → Δ ⟹ Γ ▷ A
  p {k Γ} {A : Ty k Γ} : Γ ▷ A ⟹ Γ
  q {k Γ} {A : Ty k Γ} : Tm k (Γ ▷ A) (A [ p ])

  pβ {k Δ Γ} {A : Ty k Γ} {σ : Δ ⟹ Γ} {a : Tm k Δ (A [ σ ])} : p ∘ ⟪ σ , a ⟫ = σ
  qβ {k Δ Γ} {A : Ty k Γ} {σ : Δ ⟹ Γ} {a : Tm k Δ (A [ σ ])} :
    q [ ⟪ σ , a ⟫ ] = (by rw [← substTyComp, pβ]; exact a)
  pqη {k Γ} {A : Ty k Γ} : ⟪ p (A := A) , q (A := A) ⟫ = id
  commComp {k Ξ Δ Γ} {σ : Δ ⟹ Γ} {τ : Ξ ⟹ Δ} {A : Ty k Γ} {a : Tm k Δ (A [ σ ])} :
    ⟪ σ , a ⟫ ∘ τ = ⟪ (σ ∘ τ) , (by rw [substTyComp]; exact a [ τ ]) ⟫

  consHom {k Δ Γ} (σ : Δ ⟹ Γ) (A : Ty k Γ) : Δ ▷ A [ σ ] ⟹ Γ ▷ A
    := ⟪ comp σ p , by rw [substTyComp]; exact q ⟫

  U {k Γ} : Ty k Γ
  Usubst {k Δ Γ} {σ : Δ ⟹ Γ} : U [ σ ] = U (k := k)
  TmTy {k Γ} : Tm k Γ U = Ty k Γ
end

open CwF

infix:40 "⟹" => hom
infix:70 "∘" => comp
notation:50 "•" => I
notation:60 A:61 "[" σ:61 "]" => substTy A σ
notation:60 a:61 "[" σ:61 "]" => substTm a σ
notation:50 Γ:51 "▷" A:51 => cons Γ A
notation:80 "⟪" γ:81 "," a:81 "⟫" => comm γ a
infix:70 "↑" => consHom
