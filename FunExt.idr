%default total

data Eq : forall a. a -> a -> Type where
  Refl : forall a. {x : a} -> Eq x x
  Funext : forall a, b. {f, g : (x : a) -> b x} -> (h : (x : a) -> Eq (f x) (g x)) -> Eq f g

infix 9 ==

(==): forall a. a -> a -> Type
(==) = Eq

sym : forall a, b. a == b -> b == a
sym Refl = Refl
sym (Funext h) = Funext (\x => sym (h x))

trans : forall a, b, c. a == b -> b == c -> a == c
trans Refl Refl = Refl
trans Refl (Funext h) = Funext h
trans (Funext h) Refl = Funext h
trans (Funext h1) (Funext h2) = Funext (\x => trans (h1 x) (h2 x))

param: forall a, b, c. (h : ((x : a) -> b x) -> c) -> (f, g: (x : a) -> b x) ->
  ((x : a) -> f x == g x) -> h f == h g

cong : forall a, b. (f : a -> b) -> {x, y : a} -> x == y -> f x == f y
cong f Refl = Refl
cong f (Funext h) = param f x y h

coerce : forall a, b. a == b -> a -> b
coerce Refl x = x

subst : forall a. {P : a -> Type} -> {x, y : a} -> x == y -> P x -> P y
subst Refl px = px
subst (Funext h) px = coerce (param P x y h) px
