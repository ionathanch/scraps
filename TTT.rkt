#lang racket

(require (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [test-judgment-holds  test-judgement-holds]
                    [judgment-holds       judgement-holds])
         (rename-in redex/pict
                    [render-judgment-form render-judgement-form])
         pict
         file/convertible)

;; Truncated Type Theory
(define-language TTT
  (x y f g ::= variable-not-otherwise-mentioned)
  (U ::= ★ □ △)
  (e t u ::= x (Π (x : t) t) (λ (x : t) e) (e e) (let [x e] e) U)
  (* ::= : =)
  (Γ ::= · (· (x * t) ...))

  #:binding-forms
  (Π (x : t_1) t_2 #:refers-to x)
  (λ (x : t) e #:refers-to x)
  (let [x e_1] e_2 #:refers-to x)
  #;(· (x * t) #:...bind (dom x (shadow dom x))))

(default-language TTT)
(define-syntax-rule (test-term-equal term1 term2)
  (test-equal (term term1) (term term2)))
(define-syntax-rule (test-relation-holds rel)
  (test-predicate identity (term rel)))

;; ★ is impredicative, the others are not
(define-metafunction TTT
  rule : U U -> U
  [(rule U ★) ★]
  [(rule ★ U) U]
  [(rule □ □) □]
  [(rule U △) △]
  [(rule △ U) △])

;; Extend and extract from the environment

(define-relation TTT
  :∈ ⊆ x × t × Γ
  [(:∈ x t Γ)
   (where (· _ ... (x : t) _ ...) Γ)])

(define-relation TTT
  =∈ ⊆ x × e × Γ
  [(=∈ x e Γ)
   (where (· _ ... (x = e) _ ...) Γ)])

(define-metafunction TTT
  +: : Γ x t -> Γ
  [(+: · x t) (· (x : t))]
  [(+: (· any ...) x t)
   (· any ... (x : t))])

(define-metafunction TTT
  += : Γ x e -> Γ
  [(+= · x t) (· (x = e))]
  [(+= (· any ...) x e)
   (· any ... (x = e))])

;; Other metafunctions for sequential versions of terms

(define-metafunction TTT
  Π* : (x : t) ... t -> t
  [(Π* e) e]
  [(Π* (x : t) any ... t)
   (Π (x : t) (Π* any ... t))])

(define-metafunction TTT
  λ* : (x : t) ... e -> e
  [(λ* e) e]
  [(λ* (x : t) any ... e)
   (λ (x : t) (λ* any ... e))])

(define-metafunction TTT
  @* : e e ... -> e
  [(@* e) e]
  [(@* e e_hd e_tl ...)
   (@* (e e_hd) e_tl ...)])

(define-metafunction TTT
  let* : [x e] ... e -> e
  [(let* e) e]
  [(let* [x e] any ... e_body)
   (let [x e] (let* any ... e_body))])

;; TTT is truncated because:
;; - There are only three universes, and △ itself is not a term.
;; - There is only a typed definitional equality judgement, no typing judgement.
;; - There is cumulativity for universes but no subtyping for function types.
;; Note also that in rules Π, λ, and let, the second premise context and the type
;; favour the left-hand side for the bound type or term,
;; but the right-hand version should also be derivable by symmetry.
(define-judgement-form TTT
  #:contract (⊢ Γ e e t)

  [------------ "★"
   (⊢ Γ ★ ★ □)]

  [------------ "□"
   (⊢ Γ □ □ △)]

  [(⊢ Γ t_1 t_2 ★)
   --------------- "★⊆U"
   (⊢ Γ t_1 t_2 U)]

  [(⊢ Γ t_1 t_2 U)
   ---------------- "U⊆△"
   (⊢ Γ t_1 t_2 △)]

  [(⊢ Γ e_2 e_1 t)
   --------------- "sym"
   (⊢ Γ e_1 e_2 t)]

  [(⊢ Γ e_1 e_2 t)
   (⊢ Γ e_2 e_3 t)
   --------------- "trans"
   (⊢ Γ e_1 e_3 t)]

  [(⊢ Γ e_1 e_2 t_2)
   (⊢ Γ t_1 t_2 U)
   ----------------- "conv"
   (⊢ Γ e_1 e_2 t_1)]

  [(:∈ x t Γ)
   ----------- "∈"
   (⊢ Γ x x t)]

  [(⊢ Γ t_1 t_2 U_1)
   (⊢ (+: Γ x t_1) u_1 u_2 U_2)
   -------------------------------------------------------- "Π"
   (⊢ Γ (Π (x : t_1) u_1) (Π (x : t_2) u_2) (rule U_1 U_2))]
  
  [(⊢ Γ t_1 t_2 U)
   (⊢ (+: Γ x t_1) e_1 e_2 u)
   --------------------------------------------------------- "λ"
   (⊢ Γ (λ (x : t_1) e_1) (λ (x : t_2) e_2) (Π (x : t_1) u))]

  [(⊢ Γ e_11 e_21 (Π (x : t) u))
   (⊢ Γ e_12 e_22 t)
   --------------------------------------------------- "@"
   (⊢ Γ (e_11 e_12) (e_21 e_22) (substitute u x e_12))]

  [(⊢ Γ e_11 e_21 t)
   (⊢ (+= (+: Γ x t) x e_11) e_12 e_22 u)
   ------------------------------------------------------------------- "let"
   (⊢ Γ (let [x e_11] e_12) (let [x e_21] e_22) (substitute u x e_11))]

  [(⊢ Γ t t U)
   (⊢ Γ e_2 e_2 t)
   (⊢ (+: Γ x t) e_1 e_1 u)
   ----------------------------------------------------------------------- "β"
   (⊢ Γ ((λ (x : t) e_1) e_2) (substitute e_1 x e_2) (substitute u x e_2))]

  [(⊢ Γ t t U)
   (⊢ (+: Γ x t) (e x) (e x) u)
   --------------------------------------- "η"
   (⊢ Γ (λ (x : t) (e x)) e (Π (x : t) u))]

  [(⊢ Γ e_1 e_1 t)
   (⊢ (+= (+: Γ x t) x e_1) e_2 e_2 u)
   ------------------------------------------------------------------- "ζ"
   (⊢ Γ (let [x e_1] e_2) (substitute e_2 x e_1) (substitute u x e_1))]

  [(:∈ x t Γ)
   (=∈ x e Γ)
   ----------- "δ"
   (⊢ Γ x e t)])

;; Examples

(define D-★
  (derivation
   '(⊢ · ★ ★ □) "★" '()))
(define D-★-weak
  (derivation
   '(⊢ (· (X : ★)) ★ ★ □) "★" '()))
(define D-□
  (derivation
   '(⊢ · □ □ △) "□" '()))
(define D-★△
  (derivation
   '(⊢ · ★ ★ △) "U⊆△"
   (list D-★)))

(define-term ⊥
  (Π (X : ★) X))
(test-term-equal (rule □ ★) ★)
(test-term-equal (+: · X ★) (· (X : ★)))
(test-relation-holds (:∈ X ★ (· (X : ★))))
(define D-∈
  (derivation
   '(⊢ (· (X : ★)) X X ★) "∈" '()))
(define D-⊥
  (derivation
   `(⊢ · ,(term ⊥) ,(term ⊥) ★) "Π"
   (list D-★ D-∈)))

(define D-★→★
  (derivation
   '(⊢ · (Π (X : ★) ★) (Π (X : ★) ★) □) "Π"
   (list D-★
         D-★-weak)))

(test-judgement-holds ⊢ D-★)
(test-judgement-holds ⊢ D-□)
(test-judgement-holds ⊢ D-★△)
(test-judgement-holds ⊢ D-∈)
(test-judgement-holds ⊢ D-⊥)
(test-judgement-holds ⊢ D-★→★)
(test-results)

;; Render judgment rules as image

(define (render-pretty)
  (default-style 'swiss)
  (define rules
    (with-compound-rewriters
        (['substitute (match-lambda [`(,substitute ,< ,e_body ,x ,e ,>)
                                     (list "" e_body "[" x " ↦ " e "]")])]
         ['rule (match-lambda [`(,< ,rule ,U₁ ,U₂ ,>)
                               (list rule "(" U₁ ", " U₂ ")")])]
         [':∈ (match-lambda [`(,< ,:∈ ,x ,t ,Γ ,>)
                             (list "(" x " : " t ") ∈ " Γ)])]
         ['=∈ (match-lambda [`(,< ,=∈ ,x ,e ,Γ ,>)
                             (list "(" x " ≔ " e ") ∈ " Γ)])]
         ['+: (match-lambda [`(,< ,+: ,Γ ,x ,t ,>)
                             (list Γ ", " x " : " t)])]
         ['+= (match-lambda [`(,< ,+= ,Γ ,x ,t ,>)
                             (list Γ ", " x " ≔ " t)])]
         ['let (match-lambda [`(,< ,let ,(struct* lw ([e `(,<< ,x ,e₁ ,>>)])) ,e₂ ,>)
                              (list "(let " x " ≔ " e₁ " in " e₂ ")")])]
         ['⊢ (match-lambda [`(,< ,⊢ ,Γ ,e₁ ,e₂ ,t ,>)
                            (list Γ " ⊢ " e₁ " ≡ " e₂ " : " t)])])
      #;(render-metafunction rule #:contract? #t)
      (render-judgement-form ⊢)))
  (cc-superimpose (colorize (filled-rectangle (pict-width rules) (pict-height rules)) "white") rules))

(define (render-file filename #:type type)
  (define req
    (match type
      ['png 'png@2x-bytes]
      ['svg 'svg-bytes]))
  (with-output-to-file filename
    (thunk (write-bytes (convert (render-pretty) req)))
    #:exists 'replace))