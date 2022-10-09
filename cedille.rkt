#lang racket

(require (rename-in redex/reduction-semantics
                    [define-judgment-form define-judgement-form]
                    [judgment-holds       judgement-holds]))

(define-language CDLE
  (x y ::= variable-not-otherwise-mentioned)
  (X Y ::= variable-not-otherwise-mentioned)
  (P   ::= (define (x : T) e) (define (X : k) T))
  (e t ::= (λ x e) (λ (x : T) e) (t e)
           (Λ x e) (Λ (x : T) e) (t - e)
           (Λ X e) (Λ (X : k) e) (t · U)
           [e & e] (𝟙 e) (𝟚 e)
           β (β e) (ϛ e) (e <> e) (e < T > e)
           (ρ t e) (ρ t @(λ x T) e) (φ t e e)
           (let ([x : T = e]) t) (let ([x = e]) t)
           (let ([x : T ≐ e]) t) (let ([x ≐ e]) t)
           (let ([X : k = T]) t) x)
  (T U ::= (Π (x : T) U) (T → U)
           (∀ (x : T) U) (T ⇒ U)
           (∀ (X : k) U)
           (λ x T) (λ (x : T) e) (T e)
           (λ X T) (λ (X : k) T) (T · U)
           (ι (x : T) U) {e ≃ e}
           (let ([x : T = e]) T) (let ([x = e]) T)
           (let ([X : k = T]) T) X)
  (k   ::= ⋆ (Π (x : T) k) (Π (X : k) k))

  #:binding-forms
  (λ x e #:refers-to x)
  (Λ x e #:refers-to x)
  (Λ X e #:refers-to X)
  (λ x T #:refers-to x)
  (λ X T #:refers-to X)
  (λ (x : T) e #:refers-to x)
  (Λ (x : T) e #:refers-to x)
  (Λ (X : k) e #:refers-to X)
  (λ (x : T) e #:refers-to x)
  (λ (X : k) T #:refers-to X)
  (Π (x : T) U #:refers-to x)
  (Π (x : T) k #:refers-to x)
  (Π (X : k) k #:refers-to X)
  (∀ (x : T) U #:refers-to x)
  (∀ (X : k) U #:refers-to X)
  (ι (x : T) U #:refers-to x)
  (ρ t @(λ x T #:refers-to x) e)
  (let ([x = e]) t #:refers-to x)
  (let ([x ≐ e]) t #:refers-to x)
  (let ([x = e]) T #:refers-to x)
  (let ([x : T = e]) t #:refers-to x)
  (let ([x : T ≐ e]) t #:refers-to x)
  (let ([X : k = T]) t #:refers-to X)
  (let ([x : T = e]) T #:refers-to x)
  (let ([X : k = T]) T #:refers-to X))

(define-metafunction CDLE
  let* : ([any ...] ...) any -> t or T
  [(let* () t) t]
  [(let* () T) T]
  [(let* ([x : T = e] any ...) t)
   (let ([x : T = e])
     (let* (any ...) t))]
  [(let* ([x = e] any ...) t)
   (let ([x = e])
     (let* (any ...) t))]
  [(let* ([x : T ≐ e] any ...) t)
   (let ([x : T ≐ e])
     (let* (any ...) t))]
  [(let* ([x ≐ e] any ...) t)
   (let ([x ≐ e])
     (let* (any ...) t))]
  [(let* ([X : k ≐ T] any ...) t)
   (let ([X : k ≐ T])
     (let* (any ...) t))]
  [(let* ([x : T = e] any ...) U)
   (let ([x : T = e])
     (let* (any ...) U))]
  [(let* ([x = e] any ...) U)
   (let ([x = e])
     (let* (any ...) U))]
  [(let* ([X : k ≐ T] any ...) U)
   (let ([X : k ≐ T])
     (let* (any ...) U))])