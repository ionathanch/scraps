{-
  In Theorem 2 of Section 8 of Eliminating Dependent Pattern Matching without K [1],
  they make use of the fact that UIP holds for types X with decidable equality
  (which we call discreteness) via Hedberg's theorem.
  This is proven in Theorem 1 of Section 3 of Generalizations of Hedberg's Theorem [2],
  and also discussed in On h-Propositional Reflection and Hedberg's Theorem [3],
  which links to a proof in Agda [4].
  A slightly different proof is presented in Theorem 7.2.2 of the HoTT book,
  relying on a "reflexive mere relation on X implying identity",
  i.e. (R: X -> X -> Type) ->                        -- relation on X
       (prop: (x, y: X) -> (r, s: R x y) -> r === s) -- mere propositionality of R
       (ρ: (x: X) -> R x x) ->                       -- reflexivity of R
       (f: (x, y: X) -> R x y -> x === y) -> uip X

  This file proves the original theorem, that discreteness -> UIP, not the generalization.

  [1] https://doi.org/10.1017/S0956796816000174
  [2] https://doi.org/10.1007/978-3-642-38946-7_14
  [3] https://homotopytypetheory.org/2012/11/27/on-h-propositional-reflection-and-hedbergs-theorem/
  [4] https://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html
-}

-- Basic tools of paths:
-- * J eliminator for homogenous equality
-- * inversion (symmetry)
-- * concatenation (transitivity)
-- * application (congruence)
-- * left inverse

J : forall A. (P : (x, y : A) -> (p : x === y) -> Type) -> (d : (x : A) -> P x x Refl) ->
    (x, y : A) -> (p : x === y) -> P x y p
J _ d x x Refl = d x

inv: forall A. {x, y: A} -> x === y -> y === x
inv p = J (\x, y, _ => y === x) (\x => Refl) x y p

concat: forall A. {x, y, z: A} -> x === y -> y === z -> x === z
concat p q = J (\x, y, _ => (z: A) -> y === z -> x === z) (\_, _, q => q) x y p z q

ap: forall A, B. {x, y: A} -> (f: A -> B) -> (p: x === y) -> f x === f y
ap f p = J (\x, y, _ => f x === f y) (\_ => Refl) x y p

leftInv: forall A. {x, y: A} -> (p: x === y) -> Refl === concat (inv p) p
leftInv p = J (\_, _, p => Refl === concat (inv p) p) (\_ => Refl) x y p

-- Goal: Prove UIP for some type T

uip : Type -> Type
uip t = (x, y: t) -> (p, q: x === y) -> p === q

-- Assume: Discreteness of type T,
-- i.e. decidability of equality of inhabitants of T

decidable : Type -> Type
decidable t = Either t (Not t)

discrete : Type -> Type
discrete t = (x, y: t) -> Either (x === y) (Not (x === y))

-- Intermediate properties:
-- A constant function maps everything to each other
-- A collapsible type is one with a constant endofunction
-- A path-collapsible type is one with a constant endofunction for its equality type,
-- i.e. it has an f that maps every proof of equality to each other

const: forall A, B. (A -> B) -> Type
const f = (x, y: A) -> f x === f y

collapsible: Type -> Type
collapsible t = (f: t -> t ** const f)

pathCollapsible: Type -> Type
pathCollapsible t = (x, y: t) -> collapsible (x === y)

-- We prove that discrete types are path-collapsible,
-- then that path-collapsible types have unique proofs of equality

discPathColl: discrete t -> pathCollapsible t
discPathColl disc x y =
  case disc x y of
    Left p => (\_ => p ** \_, _ => Refl)
    Right pn't => (\p => absurd (pn't p) ** \x, y => absurd (pn't x))

pathCollUIP : pathCollapsible t -> uip t
pathCollUIP pc x y p q =
  let f: forall A. {x, y: A} -> x === y -> x === y
      f = let (f ** _) = pc x y in f
      g: forall A. {x, y: A} -> (p, q: x === y) -> f p === f q
      g = let (_ ** g) = pc x y in g
      claim0: forall A. {x, y: A} -> (r: x === y) -> r === concat (inv (f Refl)) (f r)
      claim0 {x} {y} r = J (\x, y, r => r === concat (inv (f Refl)) (f r)) (\x => leftInv (f Refl)) x y r
      claim1: concat (inv (f Refl)) (f p) === concat (inv (f Refl)) (f q)
      claim1 = ap (\r => concat (inv (f Refl)) r) (g p q)
  in concat (concat (claim0 p) claim1) (inv (claim0 q))

discUIP : discrete t -> uip t
discUIP disc = (pathCollUIP (discPathColl disc))
