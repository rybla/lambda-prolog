% title: Hypothetical Scoping & Interpreter
% tags: interpreter, scope, hypothetical, imperative, shadowing
% summary: Interpreter for an imperative/functional expression and statement
%   language demonstrating block scoping, lexical variable shadowing, and local
%   environments modeled directly through hypothetical implications (=>).

module interp_scope.

kind expr type.
kind stmt type.

% Expression constructors
type elit int -> expr.
type evar string -> expr.
type eadd expr -> expr -> expr.
type esub expr -> expr -> expr.
type emul expr -> expr -> expr.
type eeq  expr -> expr -> expr.
type elt  expr -> expr -> expr.

% Statement constructors
type snop    stmt.
type sseq    stmt -> stmt -> stmt.
type slet    string -> expr -> stmt -> stmt.
type sif     expr -> stmt -> stmt -> stmt.
type sblock  stmt -> stmt.
type sresult expr -> stmt.

% Evaluation predicates
type eval_e expr -> int -> o.
type eval_b expr -> o.
type exec   stmt -> o.
type exec_res stmt -> int -> o.
type var_val string -> int -> o.

% Expression evaluation using hypothetical environment
eval_e (elit N) N.

eval_e (evar X) V :-
  var_val X V, !.

eval_e (eadd E1 E2) V :-
  eval_e E1 V1,
  eval_e E2 V2,
  V is V1 + V2.

eval_e (esub E1 E2) V :-
  eval_e E1 V1,
  eval_e E2 V2,
  V is V1 - V2.

eval_e (emul E1 E2) V :-
  eval_e E1 V1,
  eval_e E2 V2,
  V is V1 * V2.

% Boolean conditions (represented as expressions)
eval_b (eeq E1 E2) :-
  eval_e E1 V1,
  eval_e E2 V2,
  V1 = V2.

eval_b (elt E1 E2) :-
  eval_e E1 V1,
  eval_e E2 V2,
  V1 < V2.

% Statement execution
exec snop.
exec (sresult _).

exec (sseq S1 S2) :-
  exec S1,
  exec S2.

% Variable declaration with lexical scoping & shadowing:
% The new binding (var_val X V) is added hypothetically to the program.
% Because clauses are tried in LIFO order, this binding shadows any outer
% binding for the same variable X during execution of Body.
exec (slet X E Body) :-
  eval_e E V,
  (var_val X V => exec Body).

exec (sif Cond Then Else) :-
  (eval_b Cond, !, exec Then) ;
  exec Else.

% Scoped block: local declarations inside S cannot escape.
exec (sblock S) :-
  exec S.

% Statement evaluating to a final result
exec_res (sresult E) V :-
  eval_e E V.

exec_res (slet X E Body) Res :-
  eval_e E V,
  (var_val X V => exec_res Body Res).

exec_res (sseq S1 S2) Res :-
  exec S1,
  exec_res S2 Res.

exec_res (sif Cond Then Else) Res :-
  (eval_b Cond, !, exec_res Then Res) ;
  exec_res Else Res.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- exec_res (slet "x" (elit 10)
%                (slet "y" (elit 20)
%                  (sresult (eadd (evar "x") (evar "y"))))) Res.
%      Res = 30
%
%   ?- % Shadowing: outer x=10, inner x=5, result uses inner x
%      exec_res (slet "x" (elit 10)
%                (sseq (slet "x" (elit 5)
%                        (sresult (emul (evar "x") (elit 2))))
%                      (sresult (evar "x")))) Res.
%      Res = 10
