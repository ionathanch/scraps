-- Primitive
subst: forall A. (P : A -> Type) -> (x, y : A) -> (p : x === y) -> (px : P x) -> P y
subst _ x x Refl px = px

cong: forall A, B. (f: A -> B) -> (x, y: A) -> (p: x === y) -> f x === f y
cong f x y p = subst (\y => f x === f y) x y p Refl

-- Primitive
indnat: (P : Nat -> Type) -> P Z -> ((n: Nat) -> P n -> P (S n)) -> (n: Nat) -> P n
indnat _ pz pn Z = pz
indnat _ pz pn (S n) = pn n (indnat _ pz pn n)

Bottom: Type
Bottom = (A: Type) -> A

discnat: Nat -> Type
discnat n = indnat (\n => Type) Bottom (\n, pn => Nat) n

zeroOnen't: (n: Nat) -> S n === Z -> Bottom
zeroOnen't n p = subst (\t => t) Nat Bottom (cong discnat (S n) Z p) Z
