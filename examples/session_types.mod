% title: Binary Session Types & Protocol Verification
% tags: session-types, concurrency, protocols, duality, communication-safety
% summary: Binary session types following Honda, Vasconcelos, and Yoshida.
%   Enforces structured communication protocols on bidirectional channels
%   through session types: send (!T. S), receive (?T. S), internal choice /
%   selection (+{left: S1, right: S2}), external choice / branching
%   (&{left: S1, right: S2}), and termination (end). Implements protocol duality,
%   process typing, and session fidelity verification.

module session_types.

% ============================================================================
% Kinds and Syntax
% ============================================================================

kind stype   type.
kind schan   type.
kind sproc   type.
kind base_t  type.
kind msg_val type.

% Base payload types and values
type int_bt    base_t.
type bool_bt   base_t.
type string_bt base_t.

type m_int     int -> msg_val.
type m_bool    string -> msg_val.
type m_str     string -> msg_val.

type val_of    msg_val -> base_t -> o.
val_of (m_int _) int_bt.
val_of (m_bool _) bool_bt.
val_of (m_str _) string_bt.

% Session Types:
% 1. Send: !T. S  (send value of type T, continue as S)
type send_st   base_t -> stype -> stype.

% 2. Receive: ?T. S (receive value of type T, continue as S)
type recv_st   base_t -> stype -> stype.

% 3. Selection / Internal choice: +{left: S1, right: S2} (sender chooses a branch)
type select_st stype -> stype -> stype.

% 4. Branching / External choice: &{left: S1, right: S2} (receiver offers choices)
type branch_st stype -> stype -> stype.

% 5. End: protocol completed
type end_st    stype.

% ============================================================================
% Session Type Duality: S ⟂ S'
% ============================================================================

% Duality is the fundamental relation ensuring two communication endpoints
% are mutually compatible (deadlock-free and race-free).
type dual_st   stype -> stype -> o.

dual_st end_st end_st.

% Send is dual to Receive:
dual_st (send_st T S) (recv_st T S_dual) :-
  dual_st S S_dual.

% Receive is dual to Send:
dual_st (recv_st T S) (send_st T S_dual) :-
  dual_st S S_dual.

% Selection (internal choice) is dual to Branching (external choice):
dual_st (select_st S1 S2) (branch_st D1 D2) :-
  dual_st S1 D1,
  dual_st S2 D2.

dual_st (branch_st S1 S2) (select_st D1 D2) :-
  dual_st S1 D1,
  dual_st S2 D2.

% ============================================================================
% Session Processes
% ============================================================================

type inact_p   sproc.
type send_p    schan -> msg_val -> sproc -> sproc.
type recv_p    schan -> (msg_val -> sproc) -> sproc.
type sel_l_p   schan -> sproc -> sproc.
type sel_r_p   schan -> sproc -> sproc.
type branch_p  schan -> sproc -> sproc -> sproc.
type par_sp    sproc -> sproc -> sproc.

% ============================================================================
% Session Typing: s_typeof Channel SessionType Process
% ============================================================================

type s_typeof schan -> stype -> sproc -> o.

% Termination:
s_typeof _ end_st inact_p.

% Send typing:
% To send value V of type T, V must have type T, and continuation P must follow S.
s_typeof C (send_st T S) (send_p C V P) :-
  val_of V T,
  s_typeof C S P.

% Receive typing:
% Receiving on C introduces fresh bound variable v with type assumption (val_of v T).
s_typeof C (recv_st T S) (recv_p C P) :-
  pi v\ (val_of v T => s_typeof C S (P v)).

% Selection typing:
s_typeof C (select_st S1 _) (sel_l_p C P) :-
  s_typeof C S1 P.

s_typeof C (select_st _ S2) (sel_r_p C P) :-
  s_typeof C S2 P.

% Branching typing:
s_typeof C (branch_st S1 S2) (branch_p C P1 P2) :-
  s_typeof C S1 P1,
  s_typeof C S2 P2.

% Session pairing verification:
% Two processes P and Q communicating on endpoints c1 and c2 are compatible
% if P has session type S on c1, Q has session type S' on c2, and S ⟂ S'.
type session_safe schan -> schan -> stype -> sproc -> sproc -> o.

session_safe C1 C2 S P Q :-
  dual_st S S_Dual,
  s_typeof C1 S P,
  s_typeof C2 S_Dual Q.

% ============================================================================
% Example Queries & Protocol Verification
% ============================================================================

% Global endpoint names:
type ep_client, ep_server schan.

% Duality check: Send Int then Receive Bool is dual to Receive Int then Send Bool
query succeeds ?
  dual_st (send_st int_bt (recv_st bool_bt end_st))
          (recv_st int_bt (send_st bool_bt end_st)).

% Duality is symmetric / involutive:
query succeeds ?
  dual_st S (send_st int_bt end_st),
  dual_st S DualOfDual,
  DualOfDual = send_st int_bt end_st.

% Client process: sends request 42, receives boolean reply
% Server process: receives request, replies with boolean "true"
query succeeds ?
  session_safe ep_client ep_server
    (send_st int_bt (recv_st bool_bt end_st))
    (send_p ep_client (m_int 42) (recv_p ep_client (_\ inact_p)))
    (recv_p ep_server (_\ send_p ep_server (m_bool "true") inact_p)).

% Branching Protocol:
% Bank ATM protocol:
% Client selects either Balance inquiry or Deposit:
% Client: +{ Balance: ?Int. end, Deposit: !Int. ?Bool. end }
% Server: &{ Balance: !Int. end, Deposit: ?Int. !Bool. end }
query succeeds ?
  session_safe ep_client ep_server
    (select_st (recv_st int_bt end_st)
               (send_st int_bt (recv_st bool_bt end_st)))
    (sel_l_p ep_client (recv_p ep_client (_\ inact_p)))
    (branch_p ep_server
      (send_p ep_server (m_int 1000) inact_p)
      (recv_p ep_server (_\ send_p ep_server (m_bool "ok") inact_p))).

% Incompatible protocol failure (Type error / protocol mismatch):
% Client expects to send Int, but server also attempts to send Int (not dual!)
query fails ?
  session_safe ep_client ep_server
    (send_st int_bt end_st)
    (send_p ep_client (m_int 1) inact_p)
    (send_p ep_server (m_int 2) inact_p).
