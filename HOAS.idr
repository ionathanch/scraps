%default partial

namespace Direct

  mutual
    data Value : Type where
      Thunk : Comp -> Value
      Unit : Value

    data Comp : Type where
      Fource : Value -> Comp
      Return : Value -> Comp
      Let : Comp -> (Value -> Comp) -> Comp
      Lam : (Value -> Comp) -> Comp
      App : Comp -> Value -> Comp

  eval : Comp -> Comp
  eval (Fource (Thunk m)) = eval m
  eval (Return v) = Return v
  eval (Let m f) =
    case eval m of
      Return v => eval (f v)
  eval (Lam f) = Lam f
  eval (App m v) =
    case eval m of
      Lam f => eval (f v)

  test0 : eval (Return Unit) = Return Unit
  test0 = Refl

  test1 : eval (Lam Return) = Lam Return
  test1 = Refl

  test2 : eval (App (Lam Return) Unit) = Return Unit
  test2 = Refl

  test3 : eval (App (Lam (\x => Let (Fource x) Return)) (Thunk (Return Unit))) = Return Unit
  test3 = Refl

  test4 : eval (Return (Thunk (Fource (Thunk (Return Unit))))) = (Return (Thunk (Fource (Thunk (Return Unit)))))
  test4 = Refl

namespace MeijerHutton

  data MV = M | V

  data Mu : ((MV -> Type) -> (MV -> Type)) -> MV -> Type where
    Fold : k (Mu k) vm -> Mu k vm

  Unfold : Mu k vm -> k (Mu k) vm
  Unfold (Fold h) = h

  mutual
    data CBPVF : (MV -> Type) -> MV -> Type where
      ThunkF : k M -> CBPVF k V
      UnitF : CBPVF k V
      FourceF : k V -> CBPVF k M
      ReturnF : k V -> CBPVF k M
      LetF : k M -> (k V -> k M) -> CBPVF k M
      LamF : (k V -> k M) -> CBPVF k M
      AppF : k M -> k V -> CBPVF k M

  Value = Mu CBPVF V
  Comp = Mu CBPVF M

  Thunk : Comp -> Value
  Thunk m = Fold (ThunkF m)

  Unit : Value
  Unit = Fold UnitF

  Fource : Value -> Comp
  Fource v = Fold (FourceF v)

  Return : Value -> Comp
  Return v = Fold (ReturnF v)

  Let : Comp -> (Value -> Comp) -> Comp
  Let m h = Fold (LetF m h)

  Lam : (Value -> Comp) -> Comp
  Lam h = Fold (LamF h)

  App : Comp -> Value -> Comp
  App m v = Fold (AppF m v)

  dimap : (forall mv. a mv -> b mv) -> (forall mv. b mv -> a mv) -> (forall mv. CBPVF a mv -> CBPVF b mv, forall mv. CBPVF b mv -> CBPVF a mv)
  dimap f g = MkPair
    (\x => case x of
      ThunkF m => ThunkF (f m)
      UnitF => UnitF
      FourceF v => FourceF (f v)
      ReturnF v => ReturnF (f v)
      LetF m h => LetF (f m) (f . h . g)
      LamF h => LamF (f . h . g)
      AppF m v => AppF (f m) (f v))
    (\x => case x of
      ThunkF m => ThunkF (g m)
      UnitF => UnitF
      FourceF v => FourceF (g v)
      ReturnF v => ReturnF (g v)
      LetF m h => LetF (g m) (g . h . f)
      LamF h => LamF (g . h . f)
      AppF m v => AppF (g m) (g v))

  mutual
    cata : (forall mv. CBPVF k mv -> k mv) -> (forall mv. k mv -> CBPVF k mv) -> forall mv. Mu CBPVF mv -> k mv
    cata f g = f . fst (dimap (cata f g) (ana f g)) . Unfold

    ana : (forall mv. CBPVF k mv -> k mv) -> (forall mv. k mv -> CBPVF k mv) -> forall mv. k mv -> Mu CBPVF mv
    ana f g = Fold . snd (dimap (cata f g) (ana f g)) . g

  -- The (un)evaluation function is incorrect because it evaluates inside thunks and underneath lambdas;
  -- we need a paramorphism to return the original unevaluated computation

  eval : forall mv. Mu CBPVF mv -> Mu CBPVF mv
  eval = cata {k = Mu CBPVF}
    (\x => case x of
      ThunkF m => Thunk m
      UnitF => Unit
      FourceF (Fold (ThunkF m)) => m
      ReturnF v => Return v
      LetF (Fold (ReturnF v)) h => h v
      LamF h => Lam h
      AppF (Fold (LamF h)) v => h v)
    Unfold

  uneval : forall mv. Mu CBPVF mv -> Mu CBPVF mv
  uneval = ana {k = Mu CBPVF}
    (\x => case x of
      ThunkF m => Thunk m
      UnitF => Unit
      FourceF (Fold (ThunkF m)) => m
      ReturnF v => Return v
      LetF (Fold (ReturnF v)) h => h v
      LamF h => Lam h
      AppF (Fold (LamF h)) v => h v)
    Unfold

  test0 : eval (Return Unit) = Return Unit
  test0 = Refl

  -- Why does this loop??
  -- eval (Lam Return)
  -- = cata [case] Unfold (Lam Return)
  -- = [case] . fst (dimap (cata [case] Unfold) (ana [case] Unfold)) . Unfold $ (Lam Return)
  -- = [case] . fst (dimap (cata [case] Unfold) (ana [case] Unfold)) $ LamF Return
  -- = [case] . LamF (cata [case] Unfold . Return . ana [case] Unfold)
  -- = Lam (cata [case] Unfold . Return . ana [case] Unfold)
  test1 : eval (Lam Return) = Lam (?eval' . Return . MeijerHutton.uneval)
  test1 = ?Refl

  test2 : eval (App (Lam Return) Unit) = Return Unit
  test2 = Refl

  test3 : eval (App (Lam (\x => Let (Fource x) Return)) (Thunk (Return Unit))) = Return Unit
  test3 = Refl

  -- Incorrect behaviour: evaluates under thunks
  test4 : eval (Return (Thunk (Fource (Thunk (Return Unit))))) = Return (Thunk (Return Unit))
  test4 = Refl

namespace FegarasSheard

  mutual
    data Value : Type -> Type where
      Thunk : Comp b -> Value b
      Unit : Value b
      Var : b -> Value b

    data Comp : Type -> Type where
      Fource : Value b -> Comp b
      Return : Value b -> Comp b
      Let : Comp b -> (Value b -> Comp b) -> Comp b
      Lam : (Value b -> Comp b) -> Comp b
      App : Comp b -> Value b -> Comp b

  mutual
    covering
    foldValue : forall a, b.
      (thunk : b -> a) ->
      (unit : a) ->
      (fource : a -> b) ->
      (return : a -> b) ->
      (letin : b -> (a -> b) -> b) ->
      (lam : (a -> b) -> b) ->
      (app : b -> a -> b) ->
      Value a -> a
    foldValue thunk unit fource return letin lam app v =
      let foldValue' = foldValue thunk unit fource return letin lam app
          foldComp'  = foldComp  thunk unit fource return letin lam app
      in case v of
        Thunk m => thunk (foldComp' m)
        Unit => unit
        Var b => b

    covering
    foldComp : forall a, b.
      (thunk : b -> a) ->
      (unit : a) ->
      (fource : a -> b) ->
      (return : a -> b) ->
      (letin : b -> (a -> b) -> b) ->
      (lam : (a -> b) -> b) ->
      (app : b -> a -> b) ->
      Comp a -> b
    foldComp thunk unit fource return letin lam app m =
      let foldValue' = foldValue thunk unit fource return letin lam app
          foldComp'  = foldComp  thunk unit fource return letin lam app
      in case m of
        Fource v => fource (foldValue' v)
        Return v => return (foldValue' v)
        Let m h => letin (foldComp' m) (foldComp' . h . Var)
        Lam h => lam (foldComp' . h . Var)
        App m v => app (foldComp' m) (foldValue' v)

    eval : Comp (Value a) -> Comp a
    eval = snd . foldComp {a = Value a} {b = (Comp a, Comp a)}
      (\(m, _) => Thunk m)
      Unit
      (\v => case v of
        Thunk m => (Fource v, m))
      (\v => (Return v, Return v))
      (\(mi, mo), h => case mo of
        Return v => (Let mi (fst . h), snd (h v)))
      (\h => (Lam (fst . h), Lam (snd . h)))
      (\(mi, mo), v => case mo of
        Lam h => (App mi v, h v))

    mutual
      substVal : Value (Value a) -> Value a
      substVal (Thunk m) = Thunk (substCom m)
      substVal Unit = Unit
      substVal (Var x) = x

      substCom : Comp (Value a) -> Comp a
      substCom (Fource v) = Fource (substVal v)
      substCom (Return v) = Return (substVal v)
      substCom (Let m h) = Let (substCom m) (substCom . h . Var)
      substCom (Lam h) = Lam (substCom . h . Var)
      substCom (App m v) = App (substCom m) (substVal v)

    eval' : Comp (Value a) -> Comp (Value a)
    eval' (Fource (Thunk m)) = eval' m
    eval' (Return v) = Return v
    eval' (Let m h) =
      case eval' m of
        Return v => eval' (h v)
    eval' (Lam h) = Lam h
    eval' (App m v) =
      case eval' m of
        Lam h => eval' (h v)

    evaluate : (forall a. Comp a) -> (forall a. Comp a)
    evaluate m = substCom . eval' $ m

    test0 : eval (Return Unit) = Return Unit
    test0 = Refl

    test1 : eval (Lam Return) = Lam Return
    test1 = Refl

    test2 : eval (App (Lam Return) Unit) = Return Unit
    test2 = Refl

    test3 : eval (App (Lam (\x => Let (Fource x) Return)) (Thunk (Return Unit))) = Return Unit
    test3 = Refl

    test3' : eval' (App (Lam (\x => Let (Fource x) Return)) (Thunk (Return Unit))) = Return Unit
    test3' = Refl

    test4 : eval (Return (Thunk (Fource (Thunk (Return Unit))))) = (Return (Thunk (Fource (Thunk (Return Unit)))))
    test4 = Refl

    test5 : eval (App (Lam (\x => Fource x)) (Thunk (Lam (\x => Fource (Thunk (Return x)))))) = Lam (\x => Fource (Thunk (Return x)))
    test5 = Refl

    -- Incorrect behaviour: evaluates under lambdas
    test6 : eval (Lam (\x => Fource (Thunk (Return x)))) = Lam Return
    test6 = Refl

    test6' : eval' (Lam (\x => Fource (Thunk (Return x)))) = Lam (\x => Fource (Thunk (Return x)))
    test6' = Refl

    -- Incorrect behaviour: evaluates under lambdas
    test7 : eval (Let (Return Unit) (\_ => Lam (\x => Fource (Thunk (Return x))))) = Lam Return
    test7 = Refl

    test7' : eval' (Let (Return Unit) (\_ => Lam (\x => Fource (Thunk (Return x))))) = Lam (\x => Fource (Thunk (Return x)))
    test7' = Refl

    bounds : Comp Nat -> Nat
    bounds = foldComp {a = Nat} {b = Nat} id 0 id id (\n, h => n + h 1) ($ 1) (+)

    test8 : bounds (Lam Return) = 1
    test8 = Refl

    test9 : bounds (Lam (\x => Let (Fource x) Return)) = 2
    test9 = Refl

    test10 : bounds (Lam (\x => Return (Thunk (App (Fource x) x)))) = 2
    test10 = Refl

namespace STLC

  data Term : Type -> Type where
    Var : a -> Term a
    Lam : (a -> Term a) -> Term a
    App : Term a -> Term a -> Term a

  subst : Term (Term a) -> Term a
  subst (Var x) = x
  subst (Lam h) = Lam (subst . h . Var)
  subst (App m v) = App (subst m) (subst v)

  eval : Term (Term a) -> Term (Term a)
  eval (Var x) = Var x
  eval (Lam h) = Lam h
  eval (App m v) =
    case eval m of
      Lam h => eval (h (subst (eval v)))

  test : eval (App (Lam (\x => App (Var x) (Var x))) (Lam Var)) = Lam Var
  test = Refl

namespace PHOAS

  mutual
    total
    data Value : Type -> Type where
      Thunk : Comp b -> Value b
      Unit : Value b
      Var : b -> Value b

    total
    data Comp : Type -> Type where
      Fource : Value b -> Comp b
      Return : Value b -> Comp b
      Let : Comp b -> (b -> Comp b) -> Comp b
      Lam : (b -> Comp b) -> Comp b
      App : Comp b -> Value b -> Comp b

  0 Val : Type
  Val = {0 a : Type} -> Value a
  0 Com : Type
  Com = {0 a : Type} -> Comp a

  mutual
    Functor Value where
      map f (Thunk m) = Thunk (map f m)
      map f Unit = Unit
      map f (Var x) = Var (f x)

    Functor Comp where
      map f (Fource v) = Fource (map f v)
      map f (Return v) = Return (map f v)
      map f (Let m h) = Let (map f m) (\x => ?ldj)

  mutual
    covering
    substVal : Value (Value a) -> Value a
    substVal (Thunk m) = Thunk (substCom m)
    substVal Unit = Unit
    substVal (Var x) = x

    covering
    substCom : Comp (Value a) -> Comp a
    substCom (Fource v) = Fource (substVal v)
    substCom (Return v) = Return (substVal v)
    substCom (Let m h) = Let (substCom m) (substCom . h . Var)
    substCom (Lam h) = Lam (substCom . h . Var)
    substCom (App m v) = App (substCom m) (substVal v)

  eval' : Comp (Value a) -> Comp (Value a)
  eval' (Fource (Thunk m)) = eval' m
  eval' (Return v) = Return v
  eval' (Let m h) =
    case eval' m of
      Return v => eval' (h (substVal v))
  eval' (Lam h) = Lam h
  eval' (App m v) =
    case eval' m of
      Lam h => eval' (h (substVal v))

  eval : Com -> Com
  eval m = substCom . eval' $ m

  test0 : eval (Return Unit) = Return Unit
  test0 = Refl

  test1 : eval (Lam (Return . Var)) = Lam (Return . Var)
  test1 = Refl

  test2 : eval (App (Lam (Return . Var)) Unit) = Return Unit
  test2 = Refl

  -- eval (App (Lam (\x => Let (Fource (Var x)) (Return . Var))) (Thunk (Return Unit)))
  -- = Let (Fource (Var (Thunk (Return Unit)))) (Return . Var)
  -- = ?
  test3 : eval (App (Lam (\x => Let (Fource (Var x)) (Return . Var))) (Thunk (Return Unit))) = Return Unit
  test3 = Refl

  test4 : eval (Return (Thunk (Fource (Thunk (Return Unit))))) = (Return (Thunk (Fource (Thunk (Return Unit)))))
  test4 = Refl

  test5 : eval (App (Lam (\x => Fource (Var x))) (Thunk (Lam (\x => Fource (Thunk (Return (Var x))))))) = Lam (\x => Fource (Thunk (Return (Var x))))
  test5 = Refl

  -- Incorrect behaviour: evaluates under lambdas
  test6 : eval (Lam (\x => Fource (Thunk (Return (Var x))))) = Lam (Return . Var)
  test6 = Refl

  -- Incorrect behaviour: evaluates under lambdas
  test7 : eval (Let (Return Unit) (\_ => Lam (\x => Fource (Thunk (Return (Var x)))))) = Lam (Return . Var)
  test7 = Refl

