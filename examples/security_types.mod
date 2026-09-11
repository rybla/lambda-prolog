% title: Information Flow Control & Security Typing (Volpano-Smith)
% tags: security, information-flow, non-interference, lattice, type-systems
% summary: Information flow control following the Volpano-Smith-Irvine sound
%   type system. Enforces confidentiality and non-interference through a security
%   lattice (Low ⊑ High). Prevents explicit flows (Low := High) as well as implicit
%   flows through control structures (branching on High and assigning to Low)
%   via a tracked program-counter security level (pc).

module security_types.

% ============================================================================
% Security Lattice
% ============================================================================

kind sec_level type.

type sec_low   sec_level.    % Public / Low security (L)
type sec_high  sec_level.    % Secret / High security (H)

% Lattice flow relation: L1 ⊑ L2 (information at level L1 can safely flow to L2)
type sec_le    sec_level -> sec_level -> o.

sec_le sec_low sec_low.
sec_le sec_high sec_high.
% Public information can flow to Secret: Low ⊑ High
sec_le sec_low sec_high.

% Least upper bound (join): L1 ⊔ L2
type sec_join  sec_level -> sec_level -> sec_level -> o.

sec_join sec_low sec_low sec_low.
sec_join sec_low sec_high sec_high.
sec_join sec_high sec_low sec_high.
sec_join sec_high sec_high sec_high.

% ============================================================================
% Syntax of the Secure Imperative Language
% ============================================================================

kind s_expr type.
kind s_cmd  type.

% Expressions:
type s_num   int -> s_expr.
type s_var   string -> s_expr.
type s_add   s_expr -> s_expr -> s_expr.
type s_eq    s_expr -> s_expr -> s_expr.

% Commands:
type s_skip   s_cmd.
type s_assign string -> s_expr -> s_cmd.
type s_seq    s_cmd -> s_cmd -> s_cmd.
type s_if     s_expr -> s_cmd -> s_cmd -> s_cmd.
type s_while  s_expr -> s_cmd -> s_cmd.

% Variable security level classification:
type var_sec string -> sec_level -> o.

% ============================================================================
% Expression Security Level Inference: expr_level Exp Level
% ============================================================================

type expr_sec s_expr -> sec_level -> o.

% Numeric literals are constant / public:
expr_sec (s_num _) sec_low.

% Variables look up their declared security level:
expr_sec (s_var X) Lev :-
  var_sec X Lev, !.

% Compound expressions inherit the join of subexpression security levels:
expr_sec (s_add E1 E2) Lev :-
  expr_sec E1 L1,
  expr_sec E2 L2,
  sec_join L1 L2 Lev.

expr_sec (s_eq E1 E2) Lev :-
  expr_sec E1 L1,
  expr_sec E2 L2,
  sec_join L1 L2 Lev.

% ============================================================================
% Command Security Typing: pc_check PC Command
% ============================================================================

% pc_check PC Command:
% Typechecks Command under program counter security level PC.
% Invariant: Command must not write to any variable with security level lower than PC,
% preventing implicit information leakage via control flow.

type pc_check sec_level -> s_cmd -> o.

% Skip is always safe at any PC level:
pc_check _ s_skip.

% Assignment: X := E
% Requires two conditions for security:
% 1. Explicit flow: level(E) ⊑ level(X)  (no secret data written to public variable)
% 2. Implicit flow: PC ⊑ level(X)        (cannot write to public variable inside secret branch)
pc_check PC (s_assign X E) :-
  var_sec X VarLev,
  expr_sec E ExprLev,
  sec_le ExprLev VarLev,
  sec_le PC VarLev.

% Sequential composition:
pc_check PC (s_seq C1 C2) :-
  pc_check PC C1,
  pc_check PC C2.

% Conditional branching: if B then C1 else C2
% The PC level for both branches is joined with the security level of condition B:
% PC' = PC ⊔ level(B)
pc_check PC (s_if B C1 C2) :-
  expr_sec B CondLev,
  sec_join PC CondLev PC',
  pc_check PC' C1,
  pc_check PC' C2.

% While loop:
pc_check PC (s_while B C) :-
  expr_sec B CondLev,
  sec_join PC CondLev PC',
  pc_check PC' C.

% Whole-program top-level security check (starting at PC = Low):
type secure_prog s_cmd -> o.
secure_prog C :-
  pc_check sec_low C.

% ============================================================================
% Example Queries & Non-Interference Verification
% ============================================================================

% Sample variables setup:
% "secret_key" is High (H)
% "public_out" is Low (L)
% "high_scratch" is High (H)
type setup_vars o.
setup_vars :-
  (var_sec "secret_key" sec_high,
   var_sec "public_out" sec_low,
   var_sec "high_scratch" sec_high).

% 1. Safe assignment: public := public + 1 (L := L)
query succeeds ?
  (var_sec "public_out" sec_low) =>
    secure_prog (s_assign "public_out" (s_add (s_var "public_out") (s_num 1))).

% 2. Safe assignment: secret := public (H := L, safe upward flow)
query succeeds ?
  (var_sec "secret_key" sec_high,
   var_sec "public_out" sec_low) =>
    secure_prog (s_assign "secret_key" (s_var "public_out")).

% 3. Explicit leak rejection: public := secret (L := H, explicit information leak!)
% Must be REJECTED by the type system:
query fails ?
  (var_sec "public_out" sec_low,
   var_sec "secret_key" sec_high) =>
    secure_prog (s_assign "public_out" (s_var "secret_key")).

% 4. Implicit leak rejection (Control flow / covert channel):
% if (secret == 0) then public := 0 else public := 1
% Leaks the secret value into the public variable via branch condition!
% The elevated PC level (High) rejects assignment to public_out (Low).
query fails ?
  (var_sec "public_out" sec_low,
   var_sec "secret_key" sec_high) =>
    secure_prog
      (s_if (s_eq (s_var "secret_key") (s_num 0))
            (s_assign "public_out" (s_num 0))
            (s_assign "public_out" (s_num 1))).

% 5. Safe branching on secret: modifying only secret variables in branches
% if (secret == 0) then high_scratch := 0 else high_scratch := 1
query succeeds ?
  (var_sec "high_scratch" sec_high,
   var_sec "secret_key" sec_high) =>
    secure_prog
      (s_if (s_eq (s_var "secret_key") (s_num 0))
            (s_assign "high_scratch" (s_num 0))
            (s_assign "high_scratch" (s_num 1))).
