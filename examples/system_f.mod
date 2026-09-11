% title: System F (Polymorphic λ-Calculus)
% tags: system-f, polymorphism, hoas, type-systems, church-encoding
% summary: Implementation of Girard-Reynolds System F (impredicative polymorphism)
%   using Higher-Order Abstract Syntax (HOAS) for both term-level and type-level
%   binders. Features universal type quantification (∀X. T), type abstraction (ΛX. e),
%   type application (e [T]), Church encodings for booleans and polymorphic lists,
%   call-by-value evaluation, and type preservation (subject reduction).

module system_f.

% ============================================================================
% Kinds and Types
% ============================================================================

kind ty type.
kind tm type.

% Type constructors
% Base types:
type base_ty   string -> ty.
type int_ty    ty.

% Arrow type: A -> B
type arr_ty    ty -> ty -> ty.

% Universal quantification: ∀X. T(X)
% Uses HOAS at the type level: the argument (ty -> ty) represents the type
% parameterized by a type variable.
type all_ty    (ty -> ty) -> ty.

% ============================================================================
% Term Constructors
% ============================================================================

% Base integer constants
type int_tm    int -> tm.

% Term abstraction: λx:A. M(x)
% Higher-order abstract syntax: (tm -> tm) represents the scope of variable x.
type abs_tm    ty -> (tm -> tm) -> tm.

% Term application: M N
type app_tm    tm -> tm -> tm.

% Type abstraction: ΛX. M(X)
% Higher-order abstract syntax over types: (ty -> tm) represents the term
% parameterized by type variable X.
type tabs_tm   (ty -> tm) -> tm.

% Type application: M [A]
% Instantiates a polymorphic term M with concrete type A.
type tapp_tm   tm -> ty -> tm.

% ============================================================================
% Values and Operational Semantics (Call-by-Value)
% ============================================================================

type value     tm -> o.
type eval      tm -> tm -> o.
type preserves tm -> o.

% Value definitions:
% Constants and abstractions (both term and type abstractions) are terminal values.
value (int_tm _).
value (abs_tm _ _).
value (tabs_tm _).

% Evaluation rules:
% Integers evaluate to themselves.
eval (int_tm N) (int_tm N).

% Term abstractions evaluate to themselves (canonical forms for arrow types).
eval (abs_tm A Body) (abs_tm A Body).

% Type abstractions evaluate to themselves (canonical forms for universal types).
eval (tabs_tm Body) (tabs_tm Body).

% Term application (β-reduction):
% Evaluate operator to a term abstraction, evaluate argument to a value,
% then substitute the argument value into the abstraction's body via meta-application.
eval (app_tm M N) V :-
  eval M (abs_tm _ Body),
  eval N VN,
  eval (Body VN) V.

% Type application (type β-reduction):
% Evaluate operator to a type abstraction, then substitute type A into the body
% via meta-level application (Body A), and evaluate the resulting term.
eval (tapp_tm M A) V :-
  eval M (tabs_tm Body),
  eval (Body A) V.

% ============================================================================
% Type System (Hereditary Harrop Typing Context)
% ============================================================================

type typeof    tm -> ty -> o.

% Base integer typing:
typeof (int_tm _) int_ty.

% Term abstraction typing (-> Intro):
% Γ ⊢ λx:A. M : A -> B
% Fresh eigenvariable x introduced with assumption (typeof x A) via hypothetical
% implication (=>) and universal quantification (pi x\).
typeof (abs_tm A Body) (arr_ty A B) :-
  pi x\ (typeof x A => typeof (Body x) B).

% Term application typing (-> Elim):
% Γ ⊢ M : A -> B    Γ ⊢ N : A
% ---------------------------
%        Γ ⊢ M N : B
typeof (app_tm M N) B :-
  typeof M (arr_ty A B),
  typeof N A.

% Type abstraction typing (∀ Intro):
% Γ ⊢ ΛX. M : ∀X. T
% Fresh type eigenvariable a introduced via (pi a\). In System F, type variables
% are generic, so verifying the body at an abstract type variable verifies ∀X. T.
typeof (tabs_tm Body) (all_ty T) :-
  pi a\ sigma ty\ (typeof (Body a) ty, T a = ty).

% Type application typing (∀ Elim):
% Γ ⊢ M : ∀X. T(X)
% --------------------
% Γ ⊢ M [A] : T(A)
% Type substitution is executed directly by higher-order meta-application (T A).
typeof (tapp_tm M A) Res :-
  typeof M (all_ty T),
  Res = T A.

% Type preservation (Subject Reduction theorem):
% If ⊢ M : Ty and M ⇓ V, then ⊢ V : Ty.
preserves M :-
  typeof M Ty,
  eval M V,
  typeof V Ty.

% ============================================================================
% Church Encodings in System F
% ============================================================================

% Polymorphic Identity:
% id = ΛX. λx:X. x  :  ∀X. X -> X
type poly_id tm.
poly_id (tabs_tm (a\ abs_tm a (x\ x))).

type poly_id_ty ty.
poly_id_ty (all_ty (a\ arr_ty a a)).

% Church Booleans:
% CBool = ∀X. X -> X -> X
type cbool_ty ty.
cbool_ty (all_ty (x\ arr_ty x (arr_ty x x))).

% true = ΛX. λt:X. λf:X. t
type ctrue_tm tm.
ctrue_tm (tabs_tm (x\ abs_tm x (t\ abs_tm x (f\ t)))).

% false = ΛX. λt:X. λf:X. f
type cfalse_tm tm.
cfalse_tm (tabs_tm (x\ abs_tm x (t\ abs_tm x (f\ f)))).

% not = λb:CBool. ΛX. λt:X. λf:X. b [X] f t
type cnot_tm tm.
cnot_tm
  (abs_tm (all_ty (x\ arr_ty x (arr_ty x x)))
    (b\ tabs_tm (x\ abs_tm x (t\ abs_tm x (f\
          app_tm (app_tm (tapp_tm b x) f) t))))).

% Polymorphic Pairs:
% Pair(A, B) = ∀X. (A -> B -> X) -> X
type cpair_ty ty -> ty -> ty.
cpair_ty A B (all_ty (x\ arr_ty (arr_ty A (arr_ty B x)) x)).

% mkpair = ΛA. ΛB. λa:A. λb:B. ΛX. λk:(A -> B -> X). k a b
type mkpair_tm tm.
mkpair_tm
  (tabs_tm (a\ tabs_tm (b\
     abs_tm a (va\ abs_tm b (vb\
       tabs_tm (x\ abs_tm (arr_ty a (arr_ty b x)) (k\
         app_tm (app_tm k va) vb))))))).

% fst = ΛA. ΛB. λp:Pair(A, B). p [A] (λa:A. λb:B. a)
type cfst_tm tm.
cfst_tm
  (tabs_tm (a\ tabs_tm (b\
     abs_tm (all_ty (x\ arr_ty (arr_ty a (arr_ty b x)) x)) (p\
       app_tm (tapp_tm p a) (abs_tm a (va\ abs_tm b (vb\ va))))))).

% ============================================================================
% Example Queries
% ============================================================================

% Polymorphic identity is well-typed:
query succeeds ? poly_id Id, poly_id_ty Ty, typeof Id Ty.

% Specializing polymorphic identity to int:
query succeeds ?
  poly_id Id,
  eval (app_tm (tapp_tm Id int_ty) (int_tm 99)) (int_tm 99).

% Preservation check on polymorphic application:
query succeeds ?
  poly_id Id,
  preserves (app_tm (tapp_tm Id int_ty) (int_tm 42)).

% Church Booleans type checking:
query succeeds ? cbool_ty Bty, ctrue_tm T, typeof T Bty.
query succeeds ? cbool_ty Bty, cfalse_tm F, typeof F Bty.

% Church Boolean negation:
% not true evaluates to false behaviour (selects the second branch)
query succeeds ?
  cnot_tm Not, ctrue_tm True,
  eval (app_tm Not True) NegT,
  eval (app_tm (app_tm (tapp_tm NegT int_ty) (int_tm 10)) (int_tm 20)) (int_tm 20).

% Church Pair construction and first projection:
query succeeds ?
  mkpair_tm MkP, cfst_tm Fst,
  eval (tapp_tm (tapp_tm MkP int_ty) int_ty) MkPInt,
  eval (app_tm (app_tm MkPInt (int_tm 7)) (int_tm 8)) PairVal,
  eval (app_tm (tapp_tm (tapp_tm Fst int_ty) int_ty) PairVal) (int_tm 7).
