module Data.Function

infixl 1 |>
infixl 0 `on`

%inline
public export
(|>) : forall a, b. (x : a) -> ((x : a) -> b x) -> b x
(|>) x f = f x

public export
on : forall a, b. {c : forall u, v. u -> v -> Type} ->
    (g : forall w, z. (x : w) -> (y : z) -> c x y) ->
    (f : (x : a) -> b x) ->
    (x : a) -> (y : a) -> c (f x) (f y)
(on) g f = \x, y => g (f x) (f y)
