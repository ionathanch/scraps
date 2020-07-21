{-
  Some utility functions for Dec.
  Taken mostly from https://plfa.github.io/Decidable/.
  A few basic definitions come from Idris' libraries:
  * Builtin: Void, the empty type; Unit, the unit type
  * Prelude.Basics: Bool, the boolean type
  * Prelude.Uninhabited: void, the Void eliminator
  * Prelude.Types: Dec, the decidable type
-}

%default total

-- Prelude doesn't have an iff.
infix 4 <->
(<->) : Bool -> Bool -> Bool
True  <-> True  = True
False <-> False = True
_     <-> _     = False

-- Some synonyms.
xnor : Bool -> Bool -> Bool
xnor = (<->)
iff : Bool -> Bool -> Bool
iff = (<->)


T : Bool -> Type
T True  = Unit
T False = Void

TToEqual : {b : Bool} -> T b -> b = True
TToEqual {b = True} () = Refl
TToEqual {b = False} _ impossible

EqualToT : {b : Bool} -> b = True -> T b
EqualToT Refl = ()


erase : forall A. Dec A -> Bool
erase (Yes _) = True
erase (No  _) = False

toWitness : forall A. {D : Dec A} -> T (erase D) -> A
toWitness {D = Yes x} () = x
toWitness {D = No xn't} _ impossible

fromWitness : forall A. {D : Dec A} -> A -> T (erase D)
fromWitness {D = Yes x} _ = ()
fromWitness {D = No xn't} x = xn't x


infixr 6 `andDec`
andDec : forall A, B. Dec A -> Dec B -> Dec (A, B)
(Yes x)   `andDec` (Yes y)   = Yes (x, y)
(No xn't) `andDec` _         = No (\(x, _) => xn't x)
_         `andDec` (No yn't) = No (\(_, y) => yn't y)

infixr 5 `orDec`
orDec : forall A, B. Dec A -> Dec B -> Dec (Either A B)
(Yes x)   `orDec` _         = Yes (Left x)
_         `orDec` (Yes y)   = Yes (Right y)
(No xn't) `orDec` (No yn't) = No (neither xn't yn't)
  where
    neither : Not A -> Not B -> Either A B -> Void
    neither xn't _ (Left  x) = xn't x
    neither _ yn't (Right y) = yn't y

notDec : forall A. Dec A -> Dec (Not A)
notDec (Yes x)   = No ($ x)
notDec (No xn't) = Yes xn't

infixr 4 `implDec`
implDec : forall A, B. Dec A -> Dec B -> Dec (A -> B)
_         `implDec` (Yes y)   = Yes (\_ => y)
(No xn't) `implDec` _         = Yes (\x => void (xn't x))
(Yes x)   `implDec` (No yn't) = No  (\xtoy => yn't (xtoy x))

infix 4 `iffDec`
iffDec : forall A, B. Dec A -> Dec B -> Dec ((A -> B), (B -> A))
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

eraseIff : forall A, B. (x : Dec A) -> (y : Dec B) -> (erase x <-> erase y) = erase (x `iffDec` y)
eraseIff (Yes _) (Yes _) = Refl
eraseIff (Yes _) (No  _) = Refl
eraseIff (No  _) (Yes _) = Refl
eraseIff (No  _) (No  _) = Refl
