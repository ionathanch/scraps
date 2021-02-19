/* Syntactic sugar */

foralls([], T, T).
foralls([X|Xs], T, forall(X, U)) :- foralls(Xs, T, U).

/* Types */

mono(X) :- var(X).
mono(fun(T, U)) :- mono(T), mono(U).

poly(forall(X, Type)) :- var(X), poly(Type).
poly(T) :- mono(T).

/* Terms */

term(X) :- var(X).
term(app(A, B)) :- term(A), term(B).
term(lam(X, B)) :- var(X), term(B).
term(let(X, A, B)) :- var(X), term(A), term(B).

/* Contexts */

ctxt([]).
ctxt([[X|T]|Xs]) :- var(X), poly(T), ctxt(Xs).

/* Free type variables */

free(X, [X]) :- var(X).
free(fun(T, U), FVs) :-
  free(T, TFVs),
  free(U, UFVs),
  ord_union(TFVs, UFVs, FVs).
free(forall(X, T), FVs) :-
  free(T, TFVs),
  ord_del_element(TFVs, X, FVs).

free([], []).
free([[_|T]|Xs], XFVs) :-
  free(T, FV),
  free(Xs, FVs),
  ord_add_element(FVs, FV, XFVs).

/* Type substitution */

% subst(X, T, U, V) :- substitute X by T in U to produce V.
subst(X, T, X, T) :- var(X).
subst(X, _, Y, Y) :- var(X), var(Y).
subst(X, T, fun(U1, U2), fun(V1, V2)) :-
  subst(X, T, U1, V1),
  subst(X, T, U2, V2).
subst(X, _, forall(X, U), forall(X, U)).
subst(X, T, forall(Y, U), forall(Y, V)) :-
  var(X), var(Y), X \= Y,
  subst(X, T, U, V).

/* Typing rules */

specialize(T, T) :- mono(T).
specialize(forall(X, U), V) :-
  subst(X, T, U, V),
  mono(T).

check(Ctxt, X, T) :-
  member([X|T], Ctxt).
  % TODO: Specialize T
check(Ctxt, app(A, B), U) :-
  check(Ctxt, A, fun(T, U)),
  check(Ctxt, B, T).
check(Ctxt, lam(X, B), fun(T, U)) :-
  check([[X|T]|Ctxt], B, U).
check(Ctxt, let(X, A, B), V) :-
  check(Ctxt, A, T),
  free(T, AFVs),
  free(Ctxt, CFVs),
  ord_subtract(AFVs, CFVs, Xs),
  foralls(Xs, T, U),
  check([[X|U]|Ctxt], B, V).

infer(A, U) :-
  check([], A, T),
  free(T, FVs),
  foralls(FVs, T, U).
