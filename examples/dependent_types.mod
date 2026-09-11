% title: Dependent Types & Mini-LF (λΠ-Calculus)
% tags: dependent-types, lf, lambda-pi, vector, type-families, hoas
% summary: Implementation of the λΠ-calculus (the type-theoretic core of LF and
%   Martin-Löf Type Theory) with dependent function types (Π(x:A). B(x)),
%   indexed type families (length-indexed vectors vec A n), definitional
%   term conversion in types, and dependent type checking with hypothetical
%   contexts.

module dependent_types.

% ============================================================================
% Kinds and Syntax
% ============================================================================

kind dty type.
kind dtm type.

% Base types and families
type nat_dty   dty.
type bool_dty  dty.
% Length-indexed vector type family: vec_dty ElemType LengthTerm
type vec_dty   dty -> dtm -> dty.

% Dependent function type (Π-type): Π(x:A). B(x)
% Uses HOAS: (dtm -> dty) represents the type family B parameterized by term x.
type pi_dty    dty -> (dtm -> dty) -> dty.

% Simple non-dependent arrow type abbreviation constructor: A -> B
type arr_dty   dty -> dty -> dty.

% ============================================================================
% Terms
% ============================================================================

% Peano natural numbers:
type zero_dtm  dtm.
type succ_dtm  dtm -> dtm.
type plus_dtm  dtm -> dtm -> dtm.

% Booleans:
type true_dtm  dtm.
type false_dtm dtm.

% Dependent lambda abstraction: λx:A. M(x)
type lam_dtm   dty -> (dtm -> dtm) -> dtm.

% Dependent function application: M N
type app_dtm   dtm -> dtm -> dtm.

% Length-indexed vector constructors:
% vnil A : vec A 0
type vnil_dtm  dty -> dtm.

% vcons A N Head Tail : vec A (succ N)
type vcons_dtm dty -> dtm -> dtm -> dtm -> dtm.

% Vector concatenation:
% vappend A N M Vec1 Vec2 : vec A (N + M)
type vappend_dtm dty -> dtm -> dtm -> dtm -> dtm -> dtm.

% ============================================================================
% Term Evaluation & Definitional Conversion in Types
% ============================================================================

% Reduction on terms (including arithmetic reduction for index terms):
type reduce_dtm dtm -> dtm -> o.

reduce_dtm zero_dtm zero_dtm.
reduce_dtm (succ_dtm N) (succ_dtm N') :-
  reduce_dtm N N'.

reduce_dtm (plus_dtm zero_dtm M) M' :-
  reduce_dtm M M'.
reduce_dtm (plus_dtm (succ_dtm N) M) (succ_dtm Res) :-
  reduce_dtm (plus_dtm N M) Res.

reduce_dtm true_dtm true_dtm.
reduce_dtm false_dtm false_dtm.
reduce_dtm (lam_dtm A Body) (lam_dtm A Body).

reduce_dtm (app_dtm M N) Res :-
  reduce_dtm M (lam_dtm _ Body),
  reduce_dtm N VN,
  reduce_dtm (Body VN) Res.

reduce_dtm (vnil_dtm A) (vnil_dtm A).
reduce_dtm (vcons_dtm A N H T) (vcons_dtm A N' H' T') :-
  reduce_dtm N N',
  reduce_dtm H H',
  reduce_dtm T T'.

reduce_dtm X X.

% Definitional equality on types (conversion rule):
% Two types are definitionally equal if their index terms reduce to the same normal form.
type conv_ty dty -> dty -> o.

conv_ty nat_dty nat_dty.
conv_ty bool_dty bool_dty.

conv_ty (vec_dty A1 N1) (vec_dty A2 N2) :-
  conv_ty A1 A2,
  reduce_dtm N1 Norm1,
  reduce_dtm N2 Norm2,
  Norm1 = Norm2.

conv_ty (pi_dty A1 B1) (pi_dty A2 B2) :-
  conv_ty A1 A2,
  pi x\ conv_ty (B1 x) (B2 x).

conv_ty (arr_dty A1 B1) (arr_dty A2 B2) :-
  conv_ty A1 A2,
  conv_ty B1 B2.

% ============================================================================
% Dependent Type Checking
% ============================================================================

type of_dtm   dtm -> dty -> o.
type var_dty  dtm -> dty -> o.

% Natural number typing:
of_dtm zero_dtm nat_dty.
of_dtm (succ_dtm N) nat_dty :-
  of_dtm N nat_dty.
of_dtm (plus_dtm N M) nat_dty :-
  of_dtm N nat_dty,
  of_dtm M nat_dty.

% Booleans:
of_dtm true_dtm bool_dty.
of_dtm false_dtm bool_dty.

% Variable lookup from hypothetical typing context:
of_dtm X Ty :-
  var_dty X Ty, !.

% Dependent Function Abstraction (Π-Intro):
% Γ, x:A ⊢ M(x) : B(x)
% ---------------------------
% Γ ⊢ (λx:A. M(x)) : Π(x:A). B(x)
of_dtm (lam_dtm A Body) (pi_dty A B) :-
  pi x\ (var_dty x A => sigma ty\ (of_dtm (Body x) ty, conv_ty (B x) ty)).

% Simple arrow abbreviation:
of_dtm (lam_dtm A Body) (arr_dty A B) :-
  pi x\ (var_dty x A => of_dtm (Body x) B).

% Dependent Function Application (Π-Elim):
% Γ ⊢ M : Π(x:A). B(x)    Γ ⊢ N : A
% ---------------------------------
%        Γ ⊢ M N : B(N)
% The result type B(N) substitutes argument term N into type family B!
of_dtm (app_dtm M N) Res :-
  of_dtm M (pi_dty A B),
  of_dtm N Nty,
  conv_ty Nty A,
  Res = B N.

% Simple non-dependent application:
of_dtm (app_dtm M N) B :-
  of_dtm M (arr_dty A B),
  of_dtm N Nty,
  conv_ty Nty A.

% Vector Nil:
% Γ ⊢ vnil A : vec A 0
of_dtm (vnil_dtm A) (vec_dty A zero_dtm).

% Vector Cons:
% Γ ⊢ Head : A    Γ ⊢ Tail : vec A N
% ------------------------------------
% Γ ⊢ vcons A N Head Tail : vec A (succ N)
of_dtm (vcons_dtm A N Head Tail) (vec_dty A (succ_dtm N)) :-
  of_dtm Head HeadTy,
  conv_ty HeadTy A,
  of_dtm Tail (vec_dty TailA TailN),
  conv_ty TailA A,
  reduce_dtm TailN NormN,
  reduce_dtm N NormN.

% Conversion Rule (Subsumption via definitional equality):
% Γ ⊢ M : T    T ≡ T'
% -------------------- (Conv)
%      Γ ⊢ M : T'
type of_conv dtm -> dty -> o.
of_conv M Expected :-
  of_dtm M Inferred,
  conv_ty Inferred Expected.

% ============================================================================
% Example Queries
% ============================================================================

% Length-indexed vector of length 2: [true, false] : vec bool 2
query succeeds ?
  of_dtm
    (vcons_dtm bool_dty (succ_dtm zero_dtm) true_dtm
      (vcons_dtm bool_dty zero_dtm false_dtm (vnil_dtm bool_dty)))
    (vec_dty bool_dty (succ_dtm (succ_dtm zero_dtm))).

% Definitional equality checking with index computation:
% vec bool (0 + 1) is definitionally equal to vec bool 1:
query succeeds ?
  conv_ty (vec_dty bool_dty (plus_dtm zero_dtm (succ_dtm zero_dtm)))
          (vec_dty bool_dty (succ_dtm zero_dtm)).

% Vector with computed length matches expected converted type:
query succeeds ?
  of_conv
    (vcons_dtm bool_dty zero_dtm true_dtm (vnil_dtm bool_dty))
    (vec_dty bool_dty (plus_dtm zero_dtm (succ_dtm zero_dtm))).

% Dependent function: polymorphic/dependent vector head function
% vhead : Π(n:Nat). vec A (succ n) -> A
query succeeds ?
  of_dtm
    (lam_dtm nat_dty (n\
       lam_dtm (vec_dty nat_dty (succ_dtm n)) (v\
         zero_dtm)))
    (pi_dty nat_dty (n\ arr_dty (vec_dty nat_dty (succ_dtm n)) nat_dty)).

% Dependent application: applying dependent identity over natural numbers
query succeeds ?
  of_dtm
    (app_dtm (lam_dtm nat_dty (x\ x)) (succ_dtm zero_dtm))
    nat_dty.
