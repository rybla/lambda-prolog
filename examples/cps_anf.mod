% title: CPS and A-Normal Form (ANF) Transformations
% tags: cps, anf, compiler, transformation, hoas
% summary: Continuation-Passing Style (CPS) and A-Normal Form (ANF)
%   transformations using HOAS and meta-continuations to eliminate
%   administrative redexes and flatten nested subexpressions.

module cps_anf.

% Source language expressions
kind exp type.
type cst     int -> exp.
type plus_e  exp -> exp -> exp.
type mul_e   exp -> exp -> exp.
type lam_e   (exp -> exp) -> exp.
type app_e   exp -> exp -> exp.

% --- A-Normal Form (ANF) ---
% ANF guarantees all operator and function arguments are atomic values.
kind aval type.
type a_int   int -> aval.

kind aexp type.
type a_ret   aval -> aexp.
type a_plus  aval -> aval -> aexp.
type a_mul   aval -> aval -> aexp.
type a_app   aval -> aval -> aexp.
type a_let   aexp -> (aval -> aexp) -> aexp.

% ANF transformation predicate: anf Expr Continuation Result
type to_anf exp -> aexp -> o.
type anf    exp -> (aval -> aexp) -> aexp -> o.

to_anf E Out :-
  anf E (v\ a_ret v) Out.

% Constant is already atomic
anf (cst N) K (K (a_int N)).

% Variable (under binder) is atomic
anf X K (K X).

% Binary addition: convert subexpressions, bind result to fresh variable
anf (plus_e E1 E2) K Out :-
  anf E1 (v1\ anf E2 (v2\ a_let (a_plus v1 v2) (r\ K r)) Out) Out.

% Binary multiplication
anf (mul_e E1 E2) K Out :-
  anf E1 (v1\ anf E2 (v2\ a_let (a_mul v1 v2) (r\ K r)) Out) Out.

% Function application
anf (app_e E1 E2) K Out :-
  anf E1 (f\ anf E2 (arg\ a_let (a_app f arg) (r\ K r)) Out) Out.

% --- Continuation Passing Style (CPS) ---
% Target CPS terms
kind ctm type.
type c_num   int -> ctm.
type c_lam   (ctm -> (ctm -> ctm) -> ctm) -> ctm.
type c_app   ctm -> ctm -> (ctm -> ctm) -> ctm.
type c_add   ctm -> ctm -> (ctm -> ctm) -> ctm.
type c_halt  ctm -> ctm.

type to_cps exp -> ctm -> o.
type cps    exp -> (ctm -> ctm) -> ctm -> o.

to_cps E Out :-
  cps E (v\ c_halt v) Out.

% 1-pass CPS transformation using higher-order meta-continuations
cps (cst N) K (K (c_num N)).

cps X K (K X).

cps (plus_e E1 E2) K Out :-
  cps E1 (v1\ cps E2 (v2\ c_add v1 v2 K) Out) Out.

cps (lam_e Body) K (K (c_lam (x\ k\ cps (Body x) k (k x)))).

cps (app_e E1 E2) K Out :-
  cps E1 (f\ cps E2 (arg\ c_app f arg K) Out) Out.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? to_anf (plus_e (cst 1) (cst 2)) A.
query succeeds ? to_anf (plus_e (mul_e (cst 2) (cst 3)) (cst 4)) A.
query succeeds ? to_cps (plus_e (cst 10) (cst 20)) C.
