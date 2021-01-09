{-
  A proof that non-strict positive inductive types + impredicativity can yield a proof of false,
  adapted from http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/

  The axioms below correspond to the data type
    data A: Type where
      intro: ((A -> Type) -> Type) -> A
  and the pattern-matching function
      match: A -> ((A -> Type) -> Type)
      match (intro a) = a
-}

%default total

phi: Type -> Type
phi a = (a -> Type) -> Type

A: Type
intro: phi A -> A
match: A -> phi A
beta: forall a. match (intro a) === a

-- Injectivity of the constructor for A,
-- which would normally just be `cong match refl`,
-- since match (intro a) would compute
introInj: {p, q: phi A} -> intro p === intro q -> p === q
introInj refl =
  rewrite sym (beta {a = p}) in
  rewrite sym (beta {a = q}) in
  cong match refl

-- An injection from X to X -> Type
-- Note that X -> Type would have |Type|^|X| inhabitants,
-- and injectivity states that |X| <= |Type|^|X|
i: {X: Type} -> X -> X -> Type
i x y = x === y

iInj: {X: Type} -> {x, y: X} -> i x === i y -> x === y
iInj refl = rewrite cong ($ y) refl in Refl

-- An injection from (A -> Type) to A
-- Note that A -> Type would have |Type|^|A| inhabitants,
-- and injectivity states that |Type|^|A| <= |A|,
-- which clearly shouldn't hold
f: (A -> Type) -> A
f p = intro (i p)

fInj: {p, q: A -> Type} -> f p === f q -> p === q
fInj refl = iInj (introInj refl)

-- I don't really know what this is, but it roughtly corresponds to
-- the set of sets that do not contain themselves, apparently

P: A -> Type
P a = (P: A -> Type ** (f P === a, Not (P a)))

A0: A
A0 = f P

-- Show that P A0 is logically equivalent to Not (P A0)

notPA0PA0: Not (P A0) -> P A0
notPA0PA0 notPA0 = (P ** (Refl, notPA0))

PA0notPA0: P A0 -> Not (P A0)
PA0notPA0 (p ** (refl, notpa0)) pa0 =
  notpa0 (rewrite fInj {p} {q = P} refl in pa0)

-- Standard proof of Void from P A0 <-> Not (P A0)

notPA0: Not (P A0)
notPA0 pa0 = (PA0notPA0 pa0) pa0

void: Void
void = notPA0 (notPA0PA0 notPA0)
