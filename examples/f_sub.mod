% title: System F<: (Bounded Quantification & Subtyping)
% tags: f-sub, subtyping, bounded-quantification, poplmark, hoas
% summary: System F<: with kernel subtyping and bounded universal quantification
%   (∀X <: U. T), representing the formal core of the POPLmark Challenge.
%   Features contravariant arrow subtyping, reflexive and transitive subtyping,
%   higher-order type-level binders, syntax-directed subsumption, and
%   hypothetical subtyping contexts (pi x\ sub x Bound => ...).

module f_sub.

% ============================================================================
% Kinds and Types
% ============================================================================

kind ty type.
kind tm type.

% Top of the subtyping lattice: every type is a subtype of Top
type top_ty   ty.

% Base types:
type base_ty  string -> ty.
type int_ty   ty.
type bool_ty  ty.

% Arrow type constructor: S -> T
type arr_ty   ty -> ty -> ty.

% Bounded universal quantification: ∀X <: Bound. T(X)
% Uses HOAS at the type level: (ty -> ty) represents the scope of the type variable.
type all_ty   ty -> (ty -> ty) -> ty.

% ============================================================================
% Terms
% ============================================================================

% Base constants:
type int_tm   int -> tm.
type true_tm  tm.
type false_tm tm.

% Term abstraction: λx:T. M
type abs_tm   ty -> (tm -> tm) -> tm.

% Term application: M N
type app_tm   tm -> tm -> tm.

% Bounded type abstraction: ΛX <: Bound. M(X)
type tabs_tm  ty -> (ty -> tm) -> tm.

% Type application: M [A]
type tapp_tm  tm -> ty -> tm.

% ============================================================================
% Subtyping Relation (S <: T)
% ============================================================================

type sub      ty -> ty -> o.

type sub_bound ty -> ty -> o.

% Sub-Top: S <: Top for all types S
sub _ top_ty.

% Sub-Refl: Primitive reflexivity for base types
sub int_ty int_ty.
sub bool_ty bool_ty.
sub (base_ty S) (base_ty S).

% Variable bound lookup (transitivity through context):
sub X T :-
  sub_bound X U,
  sub U T.

% Sub-Arrow: Contravariant in domain, covariant in codomain
%   T1 <: S1    S2 <: T2
% ----------------------- (Sub-Arrow)
%   S1 -> S2 <: T1 -> T2
sub (arr_ty S1 S2) (arr_ty T1 T2) :-
  sub T1 S1,
  sub S2 T2.

% Sub-All (Kernel F<: rule from the POPLmark Challenge):
% The bound must match or be contravariant, and under the assumption that a fresh
% type variable x satisfies reflexivity (sub x x) and has upper bound S2 (sub_bound x S2),
% the body T1(x) is a subtype of T2(x).
sub (all_ty S1 T1) (all_ty S2 T2) :-
  sub S2 S1,
  (pi x\ ((sub x x, sub_bound x S2) => sub (T1 x) (T2 x))).

% ============================================================================
% Type System with Syntax-Directed Subsumption
% ============================================================================

type typeof   tm -> ty -> o.

typeof (int_tm _) int_ty.
typeof true_tm bool_ty.
typeof false_tm bool_ty.

% Term abstraction typing:
typeof (abs_tm A Body) (arr_ty A B) :-
  pi x\ (typeof x A => typeof (Body x) B).

% Term application with subsumption on argument:
% Γ ⊢ M : A -> B    Γ ⊢ N : A'    A' <: A
% -----------------------------------------
%                 Γ ⊢ M N : B
typeof (app_tm M N) B :-
  typeof M (arr_ty A B),
  typeof N Nty,
  sub Nty A.

% Bounded type abstraction typing:
% To typecheck ΛX <: Bound. M(X), introduce fresh type variable a with
% assumption (sub a Bound), and typecheck the body (Body a) against (T a).
typeof (tabs_tm Bound Body) (all_ty Bound T) :-
  pi a\ ((sub a a, sub_bound a Bound) => sigma ty\ (typeof (Body a) ty, T a = ty)).

% Bounded type application:
% Γ ⊢ M : ∀X <: Bound. T(X)    Γ ⊢ A <: Bound
% --------------------------------------------
%              Γ ⊢ M [A] : T(A)
typeof (tapp_tm M A) Res :-
  typeof M (all_ty Bound T),
  sub A Bound,
  Res = T A.

% ============================================================================
% Operational Semantics (CBV)
% ============================================================================

type eval     tm -> tm -> o.

eval (int_tm N) (int_tm N).
eval true_tm true_tm.
eval false_tm false_tm.
eval (abs_tm A Body) (abs_tm A Body).
eval (tabs_tm Bound Body) (tabs_tm Bound Body).

eval (app_tm M N) V :-
  eval M (abs_tm _ Body),
  eval N VN,
  eval (Body VN) V.

eval (tapp_tm M A) V :-
  eval M (tabs_tm _ Body),
  eval (Body A) V.

% ============================================================================
% Example Queries & POPLmark Verification
% ============================================================================

% Every type is a subtype of Top:
query succeeds ? sub int_ty top_ty.
query succeeds ? sub (arr_ty int_ty bool_ty) top_ty.

% Arrow subtyping:
% (Top -> Int) <: (Int -> Top) because Int <: Top (domain contravariant)
% and Int <: Top (codomain covariant).
query succeeds ? sub (arr_ty top_ty int_ty) (arr_ty int_ty top_ty).
query fails ? sub (arr_ty int_ty top_ty) (arr_ty top_ty int_ty).

% POPLmark Challenge Part 1A: Reflexivity of bounded quantifiers
% ∀X <: Int. X -> Int <: ∀X <: Int. X -> Int
query succeeds ?
  sub (all_ty int_ty (x\ arr_ty x int_ty))
      (all_ty int_ty (x\ arr_ty x int_ty)).

% Bounded universal subtyping with contravariant bounds:
% If B <: A, then (∀X <: A. X -> Top) <: (∀X <: B. X -> Top)
query succeeds ?
  sub (all_ty top_ty (x\ arr_ty x top_ty))
      (all_ty int_ty (x\ arr_ty x top_ty)).

% Bounded polymorphic function typing:
% id_top = ΛX <: Top. λx:X. x  :  ∀X <: Top. X -> X
query succeeds ?
  typeof (tabs_tm top_ty (x\ abs_tm x (v\ v)))
         (all_ty top_ty (x\ arr_ty x x)).

% Applying bounded polymorphic function to Int (Int <: Top succeeds):
query succeeds ?
  typeof (tapp_tm (tabs_tm top_ty (x\ abs_tm x (v\ v))) int_ty)
         (arr_ty int_ty int_ty).

% Evaluation of bounded type application:
query succeeds ?
  eval (app_tm
         (tapp_tm (tabs_tm top_ty (x\ abs_tm x (v\ v))) int_ty)
         (int_tm 42))
       (int_tm 42).
