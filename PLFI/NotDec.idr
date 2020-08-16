{-
  Some utility functions for Dec.
  Taken mostly from https://plfa.github.io/Negation/ and https://plfa.github.io/Decidable/.
  A few basic definitions come from Idris' libraries:
  * Builtin: Void, the empty type; Unit, the unit type
  * Prelude.Basics: Not, propositional negation; Bool, the boolean type
  * Prelude.Uninhabited: void, the Void eliminator
  * Prelude.Types: Dec, the decidable type
-}

%default total

-- Some logical definitions Prelude is missing.

infix 4 <=>
(<=>) : Bool -> Bool -> Bool
True  <=> True  = True
False <=> False = True
_     <=> _     = False

infix 4 <->
(<->) : Type -> Type -> Type
a <-> b = (a -> b, b -> a)


-- Properties of negation.

export
notNot : forall A. A -> Not (Not A)
notNot x xn't = xn't x

export
notNotNot : forall A. Not (Not (Not A)) -> (Not A)
notNotNot xn'tn'tn't x = xn'tn'tn't (notNot x)

export
contraposition : forall A, B. (A -> B) -> (Not B -> Not A)
contraposition f yn't = yn't . f

infix 4 `neq`
public export
neq : Type -> Type -> Type
neq a b = Not (a = b)

negOr : forall A, B. Not (Either A B) -> (Not A, Not B)
negOr xyn't = (\x => xyn't (Left x), \y => xyn't (Right y))

orNeg : forall A, B. (Not A, Not B) -> Not (Either A B)
orNeg (xn't, _) (Left  x) = xn't x
orNeg (_, yn't) (Right y) = yn't y

-- !(A && B) => !A || !B can't be proven
-- negAnd : forall A, B. Not (A, B) -> Either (Not A) (Not B)

andNeg : forall A, B. Either (Not A) (Not B) -> Not (A, B)
andNeg (Left  xn't) (x, _) = xn't x
andNeg (Right yn't) (_, y) = yn't y

excludedMiddleIrrefutable : forall A. Not (Not (Either A (Not A)))
excludedMiddleIrrefutable k = k (Right (\x => k (Left x)))


-- Converting between Equal, Bool, and Dec.

public export
T : Bool -> Type
T True  = Unit
T False = Void

public export
TToEqual : {b : Bool} -> T b -> b = True
TToEqual {b = True} () = Refl
TToEqual {b = False} _ impossible

public export
EqualToT : {b : Bool} -> b = True -> T b
EqualToT Refl = ()

public export
erase : forall A. Dec A -> Bool
erase (Yes _) = True
erase (No  _) = False

public export
toWitness : forall A. {D : Dec A} -> T (erase D) -> A
toWitness {D = Yes x} () = x
toWitness {D = No xn't} _ impossible

public export
toWitnessFalse : forall A. {D : Dec A} -> T (not (erase D)) -> Not A
toWitnessFalse {D = Yes x} _ impossible
toWitnessFalse {D = No xn't} () = xn't

public export
fromWitness : forall A. {D : Dec A} -> A -> T (erase D)
fromWitness {D = Yes x} _ = ()
fromWitness {D = No xn't} x = xn't x

public export
fromWitnessFalse : forall A. {D : Dec A} -> Not A -> T (not (erase D))
fromWitnessFalse {D = Yes x} xn't = xn't x
fromWitnessFalse {D = No xn't} x = ()


infixr 6 `andDec`
export
andDec : forall A, B. Dec A -> Dec B -> Dec (A, B)
(Yes x)   `andDec` (Yes y)   = Yes (x, y)
(No xn't) `andDec` _         = No (\(x, _) => xn't x)
_         `andDec` (No yn't) = No (\(_, y) => yn't y)

infixr 5 `orDec`
export
orDec : forall A, B. Dec A -> Dec B -> Dec (Either A B)
(Yes x)   `orDec` _         = Yes (Left x)
_         `orDec` (Yes y)   = Yes (Right y)
(No xn't) `orDec` (No yn't) = No (neither xn't yn't)
  where
    neither : Not A -> Not B -> Either A B -> Void
    neither xn't _ (Left  x) = xn't x
    neither _ yn't (Right y) = yn't y

export
notDec : forall A. Dec A -> Dec (Not A)
notDec (Yes x)   = No (notNot x)
notDec (No xn't) = Yes xn't

infixr 4 `implDec`
export
implDec : forall A, B. Dec A -> Dec B -> Dec (A -> B)
_         `implDec` (Yes y)   = Yes (\_ => y)
(No xn't) `implDec` _         = Yes (\x => void (xn't x))
(Yes x)   `implDec` (No yn't) = No  (\xtoy => yn't (xtoy x))

infix 4 `iffDec`
export
iffDec : forall A, B. Dec A -> Dec B -> Dec (A <-> B)
(Yes x)   `iffDec` (Yes y)   = Yes (\_ => y, \_ => x)
(No xn't) `iffDec` (No yn't) = Yes (\x => void (xn't x), \y => void (yn't y))
(No xn't) `iffDec` (Yes y)   = No (\(_, ytox) => xn't (ytox y))
(Yes x)   `iffDec` (No yn't) = No (\(xtoy, _) => yn't (xtoy x))


eraseAnd : forall A, B. (x : Dec A) -> (y : Dec B) -> (erase x && erase y) = erase (x `andDec` y)
eraseAnd (Yes _) (Yes _) = Refl
eraseAnd (Yes _) (No  _) = Refl
eraseAnd (No  _) (Yes _) = Refl
eraseAnd (No  _) (No  _) = Refl

eraseOr  : forall A, B. (x : Dec A) -> (y : Dec B) -> (erase x || erase y) = erase (x `orDec`  y)
eraseOr (Yes _) (Yes _) = Refl
eraseOr (Yes _) (No  _) = Refl
eraseOr (No  _) (Yes _) = Refl
eraseOr (No  _) (No  _) = Refl

eraseNot : forall A. (x : Dec A) -> not (erase x) = erase (notDec x)
eraseNot (Yes _) = Refl
eraseNot (No  _) = Refl

eraseIff : forall A, B. (x : Dec A) -> (y : Dec B) -> (erase x <=> erase y) = erase (x `iffDec` y)
eraseIff (Yes _) (Yes _) = Refl
eraseIff (Yes _) (No  _) = Refl
eraseIff (No  _) (Yes _) = Refl
eraseIff (No  _) (No  _) = Refl
