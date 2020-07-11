#lang racket

(require (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds])
         (rename-in redex-chk
                    [redex-judgment-holds-chk redex-judgement-holds-chk]))

;; TODOs
;; * Add some sort of η-equivalence rules to ≼
;; * Implement checking that constraints are valid and add to infer rules (...where?)
;; * Add tests for everything

;; REFERENCES
;; [0] Type Checking with Universes: https://doi.org/10.1016/0304-3975(90)90108-t
;; [1] ECC, an Extended Calculus of Constructions: https://doi.org/10.1109/lics.1989.39193
;; [2] Prop×Prop:Prop dependent pairs are "independent": https://mathoverflow.net/a/16646, https://doi.org/10.1007/bfb0018350, https://doi.org/10.1017/S0960129500001122

;; LANGUAGE
;; Luo's Extended Calculus of Constructions with:
;; * local annotated/unannotated definitions
;; * dependent pairs
;; * dependent conditionals
;; * anonymous universes

(define-language ECC
  (i j ::= natural)
  (x y α β ::= variable-not-otherwise-mentioned) ;; Term variables, Universe level variables
  (μ ν ::= i α) ;; Universe level expressions

  (x:A ::= (x : A)) ;; Assumptions
  (x=e ::= (x = e)) ;; Definitions (without type annotations)
  (x:A=e ::= (x : A = e)) ;; Definitions (with type annotations)

  (U ::= Prop Type (Type μ)) ;; Universes: Prop (impredicative), Type (anonymous), Type_i, Type_α
  (e A B ::= U x
     ;; Here, x is bound to a definition.
     ;; During reduction, we substitute all universe levels α by β.
     (x % (α ...) ↦ (β ...))
     (Π x:A B)
     (λ x:A e)
     (e e)
     (Σ x:A B)
     ([e e] as (Σ x:A B))
     (π1 e) (π2 e)
     Bool
     #t #f
     (if e then e else e return (λ (x : Bool) B))
     (let x=e in e) (let x:A=e in e))

  (c ::= (μ ≤ ν) (μ < ν)) ;; Universe level constraints
  (C ::= {c ...}) ;; Universe level constraint sets
  (Γ ::= · (Γ x:A) (Γ (C x:A=e))) ;; Environments

  (W ::= hole (W W) (π1 W) (π2 W) ;; WHNF contexts
     (if W then e else e return (λ (x : Bool) B))
     (let (x = W) in W) (let (x : A = W) in W))

  #:binding-forms
  (x : A) #:exports x
  (x : A = e) #:exports x
  (x = e) #:exports x
  (Π x:A B #:refers-to x:A)
  (λ x:A B #:refers-to x:A)
  (Σ x:A B #:refers-to x:A)
  ([e_1 e_2] as (Σ x:A B #:refers-to x:A))
  (let x:A=e in e #:refers-to x:A=e))

(default-language ECC)

;; METAFUNCTIONS

(define-metafunction ECC
  ∪ : C C -> C
  [(∪ C_1 C_2)
   {c_1 ... c_2 ...}
   (where {c_1 ...} C_1)
   (where {c_2 ...} C_2)])  

(define-metafunction ECC
  fresh : (any ...) -> α
  [(fresh (any ...))
   ,(variable-not-in (term (any ...)) (term α))])

(define-metafunction ECC
  fresh* : (any ...) (α ...) -> α
  [(fresh* (any ...) (α ...))
   ,(variables-not-in (term (any ...)) (term (α ...)))])

(define-metafunction ECC
  subst*-univ : any (α ...) (β ...) -> any
  [(subst*-univ any () ()) any]
  [(subst*-univ any (α α_r ...) (β β_r ...))
   (subst*-univ (subst-univ any α β) (α_r ...) (β_r ...))])

(define-metafunction ECC
  subst-univ : A α β -> A
  [(subst-univ (Type α) α β) (Type β)]
  [(subst-univ (Π (x : A) B) α β)
   (Π (x : (subst-univ A α β)) (subst-univ B α β))]
  [(subst-univ (λ (x : A) e) α β)
   (λ (x : (subst-univ A α β)) (subst-univ e α β))]
  [(subst-univ (e_1 e_2) α β)
   ((subst-univ e_1 α β) (subst-univ e_2 α β))]
  [(subst-univ (Σ (x : A) B) α β)
   (Σ (x : (subst-univ A α β)) (subst-univ B α β))]
  [(subst-univ ([e_1 e_2] as (Σ (x : A) B)) α β)
   ([(subst-univ e_1 α β) (subst-univ e_2 α β)] as (Σ (x : (subst-univ A α β)) (subst-univ B α β)))]
  [(subst-univ (π1 e) α β)
   (π1 (subst-univ e α β))]
  [(subst-univ (π2 e) α β)
   (π2 (subst-univ e α β))]
  [(subst-univ (if e_1 then e_2 else e_3 return (λ (x : Bool) B)) α β)
   (if (subst-univ e_1 α β) then (subst-univ e_2 α β) else (subst-univ e_3 α β) return (λ (x : Bool) (subst-univ B α β)))]
  [(subst-univ (let x = e_1 in e_2) α β)
   (let x = (subst-univ e_1 α β) in (subst-univ e_2 α β))]
  [(subst-univ (let x : A = e_1 in e_2) α β)
   (let x : (subst-univ A α β) = (subst-univ e_1 α β) in (subst-univ e_2 α β))]
  [(subst-univ e _ _) e])

(define-metafunction ECC
  LV : C -> (α ...)
  [(LV {}) ()]
  [(LV {(α_1 ≤ α_2) c ...})
   (α_1 α_2 β ...)
   (where (β ...) (LV {c ...}))]
  [(LV {(α_1 < α_2) c ...})
   (α_1 α_2 β ...)
   (where (β ...) (LV {c ...}))]
  [(LV {(i ≤ α) c ...})
   (α β ...)
   (where (β ...) (LV {c ...}))]
  [(LV {(i < α) c ...})
   (α β ...)
   (where (β ...) (LV {c ...}))]
  [(LV {(α ≤ i) c ...})
   (α β ...)
   (where (β ...) (LV {c ...}))]
  [(LV {(α < i) c ...})
   (α β ...)
   (where (β ...) (LV {c ...}))])

(define-metafunction ECC
  \\ : (α ...) (α ...) -> (α ...)
  [(\\ (α ...) ()) (α ...)]
  [(\\ (α_1 ... β α_2 ...) (β β_r ...))
   (\\ (α_1 ... α_2 ...) (β β_r ...))]
  [(\\ (α ...) (β β_r ...))
   (\\ (α ...) (β_r ...))])

(define-metafunction ECC
  Π-univ : α U U -> (U C)
  [(Π-univ _ _ Prop) (Prop {})]
  [(Π-univ α Prop (Type μ))
   ((Type α) {(μ ≤ α)})]
  [(Π-univ α (Type μ) (Type ν))
   ((Type α) {(μ ≤ α) (ν ≤ α)})])

(define-metafunction ECC
  Σ-univ : α U U -> (U C)
  [(Σ-univ _ Prop Prop) (Prop {})] ;; DANGER: Impredicative! [2]
  [(Σ-univ α (Type μ) Prop)
   ((Type α) {(μ ≤ α)})]
  [(Σ-univ α Prop (Type μ))
   ((Type α) {(μ ≤ α)})]
  [(Σ-univ α (Type μ) (Type ν))
   ((Type α) {(μ ≤ α) (ν ≤ α)})])

;; REDUCTIONS

(define (⟶ Γ)
  (reduction-relation
   ECC
   (--> (x % (α ...) ↦ (β ...))
        (subst*-univ e (α ...) (β ...))
        (judgement-holds (def _ x : _ = e ∈ (term Γ)))
        "δ")
   (--> ((λ (x : _) e_1) e_2)
        (substitute e_1 x e_2)
        "β")
   (--> (π1 ([e_1 _] as _))
        e_1
        "π1")
   (--> (π2 ([_ e_2] as _))
        e_2
        "π2")
   (--> (if #t then e_1 else _ return _)
        e_1
        "ι1")
   (--> (if #f then _ else e_2 return _)
        e_2
        "ι2")
   (--> (let (x = e_1) in e_2)
        (substitute e_2 x e_1)
        "ζ=")
   (--> (let (x : _ = e_1) in e_2)
        (substitute e_2 x e_1)
        "ζ:=")))

(define (⟶* Γ)
  (compatible-closure (⟶ Γ) ECC e))

(define (WHNF Γ)
  (context-closure (⟶ Γ) ECC W))

(define-metafunction ECC
  ▹ : Γ e -> e
  [(▹ Γ e)
   ,(apply-reduction-relation* (⟶ (term Γ)) (term e) #:cache-all? #t)])

(define-metafunction ECC
  ▹* : Γ e -> e
  [(▹* Γ e)
   ,(apply-reduction-relation* (⟶* (term Γ)) (term e) #:cache-all? #t)])

(define-metafunction ECC
  whnf : Γ e -> e
  [(whnf Γ e)
   ,(apply-reduction-relation* (WHNF (term Γ)) (term e) #:cache-all? #t)])


;; JUDGEMENTS

(define-judgement-form ECC
  #:contract (≼ Γ e e C)
  #:mode (≼ I I I O)

  [----------------------- "≼-Prop"
   (≼ Γ Prop (Type _) {})]

  [---------------------------------- "≼-Type"
   (≼ Γ (Type μ) (Type ν) {(μ ≤ ν)})]

  [(≼ Γ A_2 A_1 C_1)
   (≼ Γ A_1 A_2 C_2)
   (≼ (Γ (x_1 : A_2)) B_1 (substitute B_2 x_2 x_1) C_3)
   (where C_4 (∪ (∪ C_1 C_2) C_3))
   -------------------------------------------------- "≼-Π"
   (≼ Γ (Π (x_1 : A_1) B_1) (Π (x_2 : A_2) B_2) C_4)]

  [(≼ Γ A_1 A_2 C_1)
   (≼ (Γ (x_1 : A_2)) B_1 (substitute B_2 x_2 x_1) C_2)
   (where C_3 (∪ C_1 C_2))
   -------------------------------------------------- "≼-Σ"
   (≼ Γ (Σ (x_1 : A_1) B_1) (Σ (x_2 : A_2) B_2) C_3)]

  [(≼ Γ (whnf Γ e_1) (whnf Γ e_2) C)
   ---------------- "≼-whnf"
   (≼ Γ e_1 e_2 C)]) ;; TODO: What about η-equivalence??

(define-judgement-form ECC
  #:contract (var x : A ∈ Γ)
  #:mode (var I I O I I)

  [-------------------------- "var-∈"
   (var x : A ∈ (Γ (x : A)))]

  [(var x : A ∈ Γ)
   -------------------- "var-∉"
   (var x : A ∈ (Γ _))])

(define-judgement-form ECC
  #:contract (def C x : A = e ∈ Γ)
  #:mode (def O I I O I O I I)

  [---------------------------------------- "def-∈"
   (def C x : A = e ∈ (Γ (C (x : A = e))))]

  [(def C x : A = e ∈ Γ)
   -------------------------- "def-∉"
   (def C x : A = e ∈ (Γ _))])

(define-judgement-form ECC
  #:contract (check Γ C ⊢ e ⇐ A ↝ C e)
  #:mode (check I I I I I I I O O)

  [(infer Γ C ⊢ e ↝ C_1 e_1 ⇒ A)
   (≼ Γ A B C_2)
   ---------------------------------------- "⇐-≼"
   (check Γ C ⊢ e ⇐ B ↝ (∪ C_1 C_2) e_1)])

(define-judgement-form ECC
  #:contract (infer* Γ C ⊢ e ↝ C e ⇒* A)
  #:mode (infer* I I I I I O O I O)
  [(infer* Γ C ⊢ e ↝ C_1 e_1 ⇒ A)
   (where A_1 (whnf Γ A))
   ---------------------------------- "⇒*-whnf"
   (infer* Γ C ⊢ e ↝ C_1 e_1 ⇒* A_1)])

(define-judgement-form ECC
  #:contract (infer Γ C ⊢ e ↝ C e ⇒ A)
  #:mode (infer I I I I I O O I O)

  [(where α (fresh (Γ C)))
   (where C_1 (∪ C {(0 ≤ α)}))
   ------------------------------------------ "⇒-Prop"
   (infer Γ C ⊢ Prop ↝ C_1 Prop ⇒ (Type α))]

  [(where α (fresh (Γ C)))
   (where C_1 (∪ C {(μ < α)}))
   -------------------------------------------------- "⇒-Type_μ"
   (infer Γ C ⊢ (Type μ) ↝ C_1 (Type μ) ⇒ (Type α))]

  [(where α (fresh (Γ C)))
   (where β (fresh (Γ C α)))
   (where C_1 (∪ C {(0 ≤ β) (β < α)}))
   ------------------------------------------- "⇒-Type"
   (infer Γ C ⊢ Type ↝ C_1 (Type β) ⇒ (Type α))]

  [(var x : A ∈ Γ)
   --------------------------- "⇒-var"
   (infer Γ C ⊢ x ↝ C x ⇒ A)]

  [(def C_1 x : A = e ∈ Γ)
   (where (α ...) (\\ (LV C_1) (LV C))) ;; old
   (where (β ...) (fresh* (Γ C C_1 A e) (α ...))) ;; new
   (where C_2 (subst*-univ C_1 (α ...) (β ...)))
   (where A_0 (subst*-univ A (α ...) (β ...)))
   (where C_3 (∪ C C_2))
   ----------------------------------------------------- "⇒-def"
   (infer Γ C ⊢ x ↝ C_3 (x % (α ...) ↦ (β ...)) ⇒ A_0)]

  [(infer* Γ C ⊢ A ↝ C_1 A_1 ⇒* U_1)
   (infer* (Γ (x : A_1)) C_1 ⊢ B ↝ C_2 B_2 ⇒* U_2)
   (where α (fresh (Γ C_2 A_1 B_2 U_1 U_2)))
   (where (U C_3) (Π-univ α U_1 U_2))
   (where C_4 (∪ C_2 C_3))
   --------------------------------------------------------- "⇒-Π"
   (infer Γ C ⊢ (Π (x : A) B) ↝ C_4 (Π (x : A_1) B_2) ⇒ U)]

  [(infer* Γ C ⊢ A ↝ C_1 A_1 ⇒* U_1)
   (infer (Γ (x : A_1)) C_1 ⊢ e ↝ C_2 e_2 ⇒ B_2)
   ---------------------------------------------------------- "⇒-λ"
   (infer Γ C ⊢ (λ (x : A) e) ↝ C_2 e_2 ⇒ (Π (x : A_1) B_2))]

  [(infer* Γ C ⊢ e_1 ↝ C_1 e_11 ⇒* (Π (x : A) B))
   (check Γ C_1 ⊢ e_2 ⇐ A ↝ C_2 e_22)
   ------------------------------------------------------------------- "⇒-app"
   (infer Γ C ⊢ (e_1 e_2) ↝ C_2 (e_11 e_22) ⇒ (substitute B x e_22))]

  [(infer* Γ C ⊢ A ↝ C_1 A_1 ⇒* U_1)
   (infer* (Γ (x : A_1)) C_1 ⊢ B ↝ C_2 B_2 ⇒* U_2)
   (where α (fresh (Γ C_2 A_1 B_2 U_1 U_2)))
   (where (U C_3) (Σ-univ α U_1 U_2))
   (where C_4 (∪ C_2 C_3))
   --------------------------------------------------------- "⇒-Σ"
   (infer Γ C ⊢ (Σ (x : A) B) ↝ C_4 (Σ (x : A_1) B_2) ⇒ U)]

  [(infer Γ C ⊢ (Σ (x : A) B) ↝ C_0 (Σ (y : A_1) B_2) ⇒ U)
   (check Γ C_0 ⊢ e_1 ⇐ A_1 ↝ C_1 e_11)
   (check Γ C_1 ⊢ e_2 ⇐ (substitute B_2 y e_11) ↝ C_2 e_22)
   --------------------------------------------------------------------------------------------------------- "⇒-pair"
   (infer Γ C ⊢ ([e_1 e_2] as (Σ (x : A) B)) ↝ C_2 ([e_11 e_22] as (Σ (y : A_1) B_2)) ⇒ (Σ (y : A_1) B_2))]

  [(infer* Γ C ⊢ e ↝ C_1 e_1 ⇒* (Σ (x : A) B))
   ----------------------------------------- "⇒-π1"
   (infer Γ C ⊢ (π1 e) ↝ C_1 (π1 e_1) ⇒ A)]

  [(infer* Γ C ⊢ e ↝ C_1 e_1 ⇒* (Σ (x : A) B))
   ----------------------------------------------------------------- "⇒-π2"
   (infer Γ C ⊢ (π2 e) ↝ C_1 (π2 e_1) ⇒ (substitute B x (π1 e_1)))]

  [------------------------------------ "⇒-Bool"
   (infer Γ C ⊢ Bool ↝ C Bool ⇒ Prop)]

  [(infer* (Γ (x : Bool)) C ⊢ B ↝ C_0 B_0 ⇒* U)
   (check Γ C_0 ⊢ e_1 ⇐ Bool ↝ C_1 e_11)
   (check Γ C_1 ⊢ e_2 ⇐ (substitute B_0 x #t) ↝ C_2 e_22)
   (check Γ C_2 ⊢ e_3 ⇐ (substitute B_0 x #f) ↝ C_3 e_33)
   --------------------------------------------------------------------------------------------------------------------------------------------------------- "⇒-if"
   (infer Γ C ⊢ (if e_1 then e_2 else e_3 return (λ (x : Bool) B)) ↝ C_3 (if e_11 then e_22 else e_33 return (λ (x : Bool) B_0)) ⇒ (substitute B_0 x e_11))]

  [-------------------------------- "⇒-#t"
   (infer Γ C ⊢ #t ↝ C #t ⇒ Bool)]

  [-------------------------------- "⇒-#f"
   (infer Γ C ⊢ #f ↝ C #f ⇒ Bool)]
  
  [(infer Γ C ⊢ e_1 ↝ C_1 e_11 ⇒ A)
   (infer (Γ (C_1 (x : A = e_11))) C_1 ⊢ e_2 ↝ C_2 e_22 ⇒ B)
   ------------------------------------------------------------------------- "⇒-let="
   (infer Γ C ⊢ (let (x = e_1) in e_2) ↝ C_2 (let (x = e_11) in e_22) ⇒ B)]

  [(infer* Γ C ⊢ A ↝ C_0 A_0 ⇒* U)
   (check Γ C_0 ⊢ e_1 ⇐ A_0 ↝ C_1 e_11)
   (infer (Γ (C_1 (x : A_0 = e_11))) C_1 ⊢ e_2 ↝ C_2 e_22 ⇒ B)
   ------------------------------------------------------------------------------- "⇒-let:="
   (infer Γ C ⊢ (let (x : A = e_1) in e_2) ↝ C_2 (let (x : A_0 = e_11) e_22) ⇒ B)])