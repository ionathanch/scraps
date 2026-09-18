%unbound_implicits off

data U : Type where
  Mk : forall X. (1 _ : (1 _ : X) -> U) -> U

1 loop : U
loop = Mk {X = U} (\x => x)

data WF : U -> Type where
  Wf : forall X. {0 f : (1 _ : X) -> U} -> (1 _ : (1 x : X) -> WF (f x)) -> WF (Mk f)

1 wfu : (1 x : U) -> WF x
wfu (Mk f) = Wf (\x => wfu (f x))

1 nwf : (1 _ : WF loop) -> Void
nwf (Wf h) = nwf (h loop)

1 false : Void
false = nwf (wfu loop)
