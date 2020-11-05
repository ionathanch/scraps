-- Basic facts: id, J eliminator, ap (cong), subst (eq_rect), <> (concat/trans), ~~ (homotopy)

id : (A : Type) -> A -> A
id _ a = a

J : forall A. (P : (x, y : A) -> (p : x === y) -> Type) -> (d : (x : A) -> P x x Refl) ->
  (x, y : A) -> (p : x === y) -> P x y p
J _ d x x Refl = d x

ap : forall A, B. (f : A -> B) -> {x, y : A} -> x === y -> f x === f y
ap f p =
  J (\x, y, p => f x === f y)
    (\x => Refl)
    x y p

subst : forall A. {P : A -> Type} -> (x, y : A) -> x === y -> P x -> P y
subst x y p =
  J (\x, y, p => P x -> P y)
    (\x, px => px)
    x y p

infixr 8 <>
(<>) : forall A. {x, y, z : A} -> x === y -> y === z -> x === z
p <> q =
  J (\x, y, p => (z : A) -> y === z -> x === z)
    (\x, z, xz => xz)
    x y p z q

infix 5 ~~
(~~) : forall A, P. (f, g : (x : A) -> P x) -> Type
f ~~ g = (x : A) -> f x === g x

-- Some general lemmas

-- Find a homotopy between (retract . f) and (ap f . section)
-- This is done in Coq here: https://github.com/HoTT/HoTT/blob/master/theories/Basics/Equivalences.v#L130
-- Or in Idris here: https://github.com/ionathanch/HoTT-Idris/blob/master/Equivalences.idr#L108
-- Both are fairly involved, so I'll leave this alone
retsec : forall A, B. (f : A -> B) -> (g : B -> A) ->
  (section : g . f ~~ id A) -> (retract : f . g ~~ id B) ->
  (a : A) -> retract (f a) === (ap f (section a))

-- We can "peel" an f off of the path and stick it at the end of the goal P
subst_lem1 : forall A, B. {P : B -> Type} -> (f : A -> B) ->
  (x, y : A) -> (p : x === y) -> (pfx : P (f x)) ->
  subst {P} (f x) (f y) (ap f p) pfx = subst {P = P . f} x y p pfx
subst_lem1 f x y p pfx =
  J (\x, y, p => (pfx : P (f x)) -> subst {P} (f x) (f y) (ap f p) pfx = subst {P = P . f} x y p pfx)
    (\x, pfx => Refl)
    x y p pfx

-- I think this is just ap in disguise
subst_lem2 : forall A, B. {P : A -> Type} -> (f : (x : A) -> P x) ->
  (x, y : A) -> (p : x === y) ->
  subst {P} x y p (f x) === f y
subst_lem2 f x y p =
  J (\x, y, p => subst {P} x y p (f x) === f y)
    (\x => Refl)
    x y p

-- Collecting puzzle pieces...

puzzle_lem0 : forall A, B. {P : B -> Type} -> (f : A -> B) -> (g : B -> A) ->
  (section : g . f ~~ id A) -> (retract : f . g ~~ id B) ->
  (a : A) -> (f0 : (a : A) -> P (f a)) ->
  subst {P} (f (g (f a))) (f a) (retract (f a)) (f0 (g (f a))) === subst {P} (f (g (f a))) (f a) (ap f (section a)) (f0 (g (f a)))
puzzle_lem0 f g section retract a f0 =
  ap (\p => subst {P} (f (g (f a))) (f a) p (f0 (g (f a))))
    (retsec f g section retract a)

puzzle_lem1 : forall A, B. {P : B -> Type} -> (f : A -> B) -> (g : B -> A) ->
  (section : g . f ~~ id A) -> (a : A) -> (f0 : (a : A) -> P (f a)) ->
  subst {P} (f (g (f a))) (f a) (ap f (section a)) (f0 (g (f a))) === subst {P = P . f} (g (f a)) a (section a) (f0 (g (f a)))
puzzle_lem1 f g section a f0 = subst_lem1 {A} {B} {P} f (g (f a)) a (section a) (f0 (g (f a)))

puzzle_lem2 : forall A, B. {P : B -> Type} -> (f : A -> B) -> (g : B -> A) ->
  (section : g . f ~~ id A) -> (a : A) -> (f0 : (a : A) -> P (f a)) ->
  subst {P = P . f} (g (f a)) a (section a) (f0 (g (f a))) === f0 a
puzzle_lem2 f g section a f0 = subst_lem2 {A} {B} {P = P . f} f0 (g (f a)) a (section a)

-- Now put the puzzle pieces together

puzzle : forall A, B. {P : B -> Type} -> (f : A -> B) -> (g : B -> A) ->
  (section : g . f ~~ id A) -> (retract : f . g ~~ id B) ->
  (a : A) -> (f0 : (a : A) -> P (f a)) ->
  subst {P} (f (g (f a))) (f a) (retract (f a)) (f0 (g (f a))) === f0 a
puzzle f g section retract a f0 =
  (puzzle_lem0 {P} f g section retract a f0)
  <> (puzzle_lem1 {P} f g section a f0)
  <> (puzzle_lem2 {P} f g section a f0)
