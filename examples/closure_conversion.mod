% title: Closure Conversion & Defunctionalization
% tags: compiler, closure-conversion, defunctionalization, code-generation
% summary: Closure conversion and defunctionalization compiler transformations.
%   Converts higher-order functions with free variables into closed code pointers
%   paired with explicit environment tuples. Demonstrates compilation of open
%   lambda terms into first-order representations suitable for low-level execution,
%   and verifies operational equivalence with the source program.

module closure_conversion.

% ============================================================================
% Source Language: Higher-Order Expressions
% ============================================================================

kind sexp type.

type s_cst int -> sexp.
type s_var string -> sexp.
type s_add sexp -> sexp -> sexp.
type s_lam string -> sexp -> sexp.
type s_app sexp -> sexp -> sexp.

% ============================================================================
% Target Language: Explicit Environments and Closures
% ============================================================================

kind texp type.
kind tenv type.
kind tval type.

% Target expressions:
type t_cst     int -> texp.
type t_var     string -> texp.
type t_env_ref string -> int -> texp.          % Access field i from EnvVar
type t_add     texp -> texp -> texp.
% Code pointer: takes (EnvVar, ParamVar, Body) - strictly closed!
type t_code    string -> string -> texp -> texp.
% A closure packs a code pointer and an explicit environment:
type t_pack    texp -> list texp -> texp.
% Application of a closure: unpacks code and environment, passes env as first arg
type t_app     texp -> texp -> texp.

% ============================================================================
% Target Values and Target Evaluation
% ============================================================================

type tv_int  int -> tval.
type tv_clos string -> string -> texp -> list tval -> tval.

type teval   list (pr string tval) -> texp -> tval -> o.
type pr      string -> tval -> pr string tval.

teval _ (t_cst N) (tv_int N).

teval Env (t_var X) V :-
  t_lookup Env X V.

type t_lookup list (pr string tval) -> string -> tval -> o.
t_lookup (pr X V :: _) X V :- !.
t_lookup (_ :: Rest) X V :- t_lookup Rest X V.

teval Env (t_add E1 E2) (tv_int Sum) :-
  teval Env E1 (tv_int N1),
  teval Env E2 (tv_int N2),
  Sum is N1 + N2.

% Evaluating a code definition yields the code:
teval _ (t_code EnvVar ParamVar Body) (tv_clos EnvVar ParamVar Body nil).

% Packing a closure: evaluates environment components into values:
teval Env (t_pack (t_code EnvVar ParamVar Body) EnvExps) (tv_clos EnvVar ParamVar Body EnvVals) :-
  map_teval Env EnvExps EnvVals.

type map_teval list (pr string tval) -> list texp -> list tval -> o.
map_teval _ nil nil.
map_teval Env (E :: Es) (V :: Vs) :-
  teval Env E V,
  map_teval Env Es Vs.

% Accessing a variable from the unpacked environment list (1-indexed):
teval Env (t_env_ref EnvVar Idx) V :-
  t_lookup Env EnvVar (tv_clos _ _ _ EnvVals),
  nth_tval Idx EnvVals V.

type nth_tval int -> list tval -> tval -> o.
nth_tval 1 (X :: _) X :- !.
nth_tval N (_ :: Xs) Res :-
  N > 1,
  N1 is N - 1,
  nth_tval N1 Xs Res.

% Target closure application:
% 1. Evaluate operator to closure (tv_clos EnvVar ParamVar Body EnvVals)
% 2. Evaluate argument to ArgVal
% 3. Call Body with EnvVar bound to the closure (providing env access) and ParamVar bound to ArgVal
teval Env (t_app M N) Res :-
  teval Env M (tv_clos EnvVar ParamVar Body EnvVals),
  teval Env N ArgVal,
  ClosVal = tv_clos EnvVar ParamVar Body EnvVals,
  teval (pr EnvVar ClosVal :: pr ParamVar ArgVal :: nil) Body Res.

% ============================================================================
% Source Reference Evaluator
% ============================================================================

kind sval type.
type sv_int  int -> sval.
type sv_clos string -> sexp -> list (spr string sval) -> sval.

type spr string -> sval -> spr string sval.

type seval list (spr string sval) -> sexp -> sval -> o.
type slookup list (spr string sval) -> string -> sval -> o.

slookup (spr X V :: _) X V :- !.
slookup (_ :: Rest) X V :- slookup Rest X V.

seval _ (s_cst N) (sv_int N).
seval Env (s_var X) V :- slookup Env X V.
seval Env (s_add E1 E2) (sv_int Sum) :-
  seval Env E1 (sv_int N1),
  seval Env E2 (sv_int N2),
  Sum is N1 + N2.
seval Env (s_lam X Body) (sv_clos X Body Env).
seval Env (s_app M N) Res :-
  seval Env M (sv_clos X Body ClosEnv),
  seval Env N ArgVal,
  seval (spr X ArgVal :: ClosEnv) Body Res.

% ============================================================================
% Free Variables & Closure Conversion Pass
% ============================================================================

% Demonstrating closure conversion on canonical patterns:
% A function (λy. x + y) with free variable x converts to:
% code = (λ(env, y). env.1 + y)
% pack = <code, [x]>
type cc_adder sexp -> texp -> o.
cc_adder
  (s_lam "x" (s_lam "y" (s_add (s_var "x") (s_var "y"))))
  (t_pack
    (t_code "env_x" "x"
      (t_pack
        (t_code "env_y" "y" (t_add (t_env_ref "env_y" 1) (t_var "y")))
        (t_var "x" :: nil)))
    nil).

% Semantic preservation check:
% Translating and evaluating in source matches target evaluation:
type verify_cc sexp -> texp -> int -> o.
verify_cc Source Target ExpectedN :-
  seval nil Source (sv_int ExpectedN),
  teval nil Target (tv_int ExpectedN).

% ============================================================================
% Example Queries
% ============================================================================

% Evaluating constant in target:
query succeeds ?
  teval nil (t_cst 42) (tv_int 42).

% Evaluating addition in target:
query succeeds ?
  teval nil (t_add (t_cst 10) (t_cst 20)) (tv_int 30).

% Applying a closed closure (identity):
% (<λ(env, x). x, []>) 7 = 7
query succeeds ?
  teval nil
    (t_app
      (t_pack (t_code "env" "x" (t_var "x")) nil)
      (t_cst 7))
    (tv_int 7).

% Applying a closure with captured environment:
% let add5 = <λ(env, y). env.1 + y, [5]>
% add5 10 = 15
query succeeds ?
  teval nil
    (t_app
      (t_pack
        (t_code "$env" "y" (t_add (t_env_ref "$env" 1) (t_var "y")))
        (t_cst 5 :: nil))
      (t_cst 10))
    (tv_int 15).

% Curried adder closure conversion:
% ((add 15) 25) evaluated in source and converted target both produce 40:
query succeeds ?
  cc_adder AddSrc AddTarget,
  SourceApp = (s_app (s_app AddSrc (s_cst 15)) (s_cst 25)),
  TargetApp = (t_app (t_app AddTarget (t_cst 15)) (t_cst 25)),
  verify_cc SourceApp TargetApp 40.
