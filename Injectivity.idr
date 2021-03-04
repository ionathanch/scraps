%default total

data Size: Type where
  Base: Size
  Next: Size -> Size

J : forall A. (P : (x, y : A) -> (p : x = y) -> Type) -> (d : (x : A) -> P x x Refl) ->
  (x, y : A) -> (p : x = y) -> P x y p
J _ d x x Refl = d x

injRefl: {r, s: Size} -> Next r = Next s -> r = s
injRefl Refl = Refl

injJ: {r, s: Size} -> Next r = Next s -> r = s
injJ p = J P d (Next r) (Next s) p
  where
    P: (r, s: Size) -> (p: r = s) -> Type
    P (Next r) (Next s) _ = r = s
    P Base Base _ = Unit
    d: (s: Size) -> P s s Refl
    d (Next s) = Refl
    d Base = ()

injCase: {r, s: Size} -> Next r = Next s -> r = s
injCase p =
  case p of
    Refl {x = Next s} => Refl {x = s}
