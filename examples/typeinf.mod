% title: Simply-typed λ-calculus
% tags: library, hoas, pi, implication
% summary: STLC with HOAS: base types, pairs, booleans, type inference,
%   and the types of the I/K combinators.

module typeinf.

kind tm  type.
kind ty  type.

type app      tm -> tm -> tm.
type abs      (tm -> tm) -> tm.
type c        tm.
type unit_val tm.
type true, false  tm.
type if       tm -> tm -> tm -> tm.
type mkpair   tm -> tm -> tm.
type fst, snd tm -> tm.
type inl_tm   ty -> tm -> tm.
type inr_tm   ty -> tm -> tm.
type case_tm  tm -> (tm -> tm) -> (tm -> tm) -> tm.
type fix      ty -> (tm -> tm) -> tm.
type arrow    ty -> ty -> ty.
type prod     ty -> ty -> ty.
type sum      ty -> ty -> ty.
type i, bool, unit_t ty.
type of       tm -> ty -> o.
type hastype  tm -> o.
type ident_ty ty -> o.
type const_ty ty -> ty -> o.

of c i.
of unit_val unit_t.
of true bool.
of false bool.

of (abs M) (arrow A B) :-
  pi x\ (of x A => of (M x) B).
of (app M N) B :-
  of M (arrow A B), of N A.
of (if M N P) A :-
  of M bool, of N A, of P A.
of (mkpair M N) (prod A B) :-
  of M A, of N B.
of (fst M) A :- of M (prod A _).
of (snd M) B :- of M (prod _ B).
of (inl_tm B M) (sum A B) :- of M A.
of (inr_tm A N) (sum A B) :- of N B.
of (case_tm M L R) C :-
  of M (sum A B),
  (pi x\ of x A => of (L x) C),
  (pi y\ of y B => of (R y) C).
of (fix A Body) A :-
  pi x\ of x A => of (Body x) A.

hastype M :- of M _.

% Identity: ⊢ λx. x : A → A
ident_ty (arrow A A) :- of (abs (x\ x)) (arrow A A).

% K combinator: ⊢ λx. λy. x : A → B → A
const_ty A B :- of (abs (x\ abs (y\ x))) (arrow A (arrow B A)).

query succeeds ? of (abs (y\ y)) (arrow A A).
query succeeds ? of (app (abs (x\ x)) c) i.
query succeeds ? of true bool.
query succeeds ? of (if true c c) i.
query succeeds ? of (mkpair c true) (prod i bool).
query succeeds ? of (fst (mkpair c true)) i.
query succeeds ? ident_ty T.
query succeeds ? const_ty i bool.
query succeeds ? hastype (abs (x\ app x c)).
