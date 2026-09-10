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
type true, false  tm.
type if       tm -> tm -> tm -> tm.
type mkpair   tm -> tm -> tm.
type fst, snd tm -> tm.
type arrow    ty -> ty -> ty.
type prod     ty -> ty -> ty.
type i, bool  ty.
type of       tm -> ty -> o.
type hastype  tm -> o.
type ident_ty ty -> o.
type const_ty ty -> ty -> o.

of c i.
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

hastype M :- of M _.

% Identity: ⊢ λx. x : A → A
ident_ty (arrow A A) :- of (abs (x\ x)) (arrow A A).

% K combinator: ⊢ λx. λy. x : A → B → A
const_ty A B :- of (abs (x\ abs (y\ x))) (arrow A (arrow B A)).

% ---------------------------------------------------------------------------
% Examples
%   ?- of (abs (y\ y)) (arrow A A).
%   ?- of (app (abs (x\ x)) c) i.
%   ?- of true bool.
%   ?- of (if true c c) i.
%   ?- of (mkpair c true) (prod i bool).
%   ?- of (fst (mkpair c true)) i.
%   ?- ident_ty T.
%   ?- const_ty i bool.
%   ?- hastype (abs (x\ app x c)).
