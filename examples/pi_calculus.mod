% title: The π-Calculus & Scope Extrusion
% tags: pi-calculus, concurrency, process-calculi, hoas, scope-extrusion
% summary: Encoding of the polyadic/monadic π-calculus following Dale Miller's
%   foundational work on higher-order process calculi. Restriction (νx. P) and
%   input prefixes (x(y). P) are represented via HOAS, using meta-level
%   quantification (pi) for fresh channel creation. Features a labeled transition
%   system (LTS), reaction semantics, and channel scope extrusion.

module pi_calculus.

% ============================================================================
% Kinds and Syntax
% ============================================================================

kind chan type.
kind proc type.

% Base process constructors:
type nil_p    proc.                          % 0 (inert process)
type out_p    chan -> chan -> proc -> proc.  % x<y>. P (output channel y on channel x)
type in_p     chan -> (chan -> proc) -> proc.% x(y). P (input y on x, binding y in P)
type par_p    proc -> proc -> proc.          % P | Q   (parallel composition)
type nu_p     (chan -> proc) -> proc.        % (νx) P  (private channel restriction)
type tau_p    proc -> proc.                  % τ. P    (silent internal action)

% ============================================================================
% Labeled Actions for the Transition System
% ============================================================================

kind act type.
type tau_act  act.                           % τ silent action
type out_act  chan -> chan -> act.           % x!y (free output of y on x)
type in_act   chan -> chan -> act.           % x?y (input of y on x)
type bout_act chan -> act.                   % (νy) x!y (bound output: scope extrusion)

% Transition predicate: trans P Action P'
% Process P performs Action and transitions to P'
type trans    proc -> act -> proc -> o.

% Tau step:
trans (tau_p P) tau_act P.

% Output action: x<y>. P performs output of y on x:
trans (out_p X Y P) (out_act X Y) P.

% Input action: x(y). P performs input of any available name Z on x:
trans (in_p X Body) (in_act X Z) (Body Z).

% Restriction: (νx) P
% Actions not mentioning the restricted channel x pass through unaffected.
% Name freshness is enforced by universal quantification (pi x\).
trans (nu_p Body) Act (nu_p Body') :-
  pi x\ (trans (Body x) Act (Body' x)).

% Scope Extrusion (Open rule):
% If Body(y) outputs the restricted private name y on public channel X,
% the boundary opens and the action becomes a bound output (bout_act X):
%
%      P(y) ───X!y───> P'(y)
% -------------------------------- (Open)
%  (νy) P(y) ───(ν)X!───> λy. P'(y)
type trans_open proc -> chan -> (chan -> proc) -> o.

trans_open (nu_p Body) X ResBody :-
  pi y\ (trans (Body y) (out_act X y) (ResBody y)).

% Parallel Left: P | Q steps if P steps:
trans (par_p P Q) Act (par_p P' Q) :-
  trans P Act P'.

% Parallel Right: P | Q steps if Q steps:
trans (par_p P Q) Act (par_p P Q') :-
  trans Q Act Q'.

% Synchronization / Communication (Close / Com rules):
% 1. Free communication between matching output and input:
% P ───X!Y───> P'    Q ───X?Y───> Q'
% ---------------------------------- (Com-L)
%        P | Q ───τ───> P' | Q'
trans (par_p P Q) tau_act (par_p P' Q') :-
  trans P (out_act X Y) P',
  trans Q (in_act X Y) Q'.

trans (par_p P Q) tau_act (par_p P' Q') :-
  trans P (in_act X Y) P',
  trans Q (out_act X Y) Q'.

% 2. Scope Extrusion Synchronization (Close rule):
% One process performs bound output of its private name y, which enters the scope of Q!
%
%  P ───(ν)X!───> P'(y)    Q ───X?y───> Q'(y)
% ------------------------------------------- (Close)
%          P | Q ───τ───> (νy) (P'(y) | Q'(y))
trans (par_p P Q) tau_act (nu_p (y\ par_p (P' y) (Q' y))) :-
  trans_open P X P',
  pi y\ trans Q (in_act X y) (Q' y).

trans (par_p P Q) tau_act (nu_p (y\ par_p (P' y) (Q' y))) :-
  trans_open Q X Q',
  pi y\ trans P (in_act X y) (P' y).

% ============================================================================
% Multi-Step Reaction: P ⟶* P'
% ============================================================================

type reacts    proc -> proc -> o.
type reacts_to proc -> proc -> o.

% One reaction step is a silent tau transition:
reacts P P' :-
  trans P tau_act P'.

% Multi-step reflexive transitive closure of reaction:
reacts_to P P.
reacts_to P P'' :-
  reacts P P',
  reacts_to P' P''.

% ============================================================================
% Example Queries
% ============================================================================

% Global channels:
type c_pub, c_data, c_ack chan.

% Basic message passing: x<data>.0 | x(y). y<ack>.0  ⟶  0 | data<ack>.0
query succeeds ?
  reacts
    (par_p (out_p c_pub c_data nil_p)
           (in_p c_pub (y\ out_p y c_ack nil_p)))
    (par_p nil_p (out_p c_data c_ack nil_p)).

% Scope Extrusion:
% A process creates private channel secret, and exports it on public channel c_pub:
% (νs) (c_pub<s>.0) | c_pub(z). z<ack>.0
% The private scope of s extrudes to enclose the receiver:
% (νs) (0 | s<ack>.0)
query succeeds ?
  reacts
    (par_p (nu_p (s\ out_p c_pub s nil_p))
           (in_p c_pub (z\ out_p z c_ack nil_p)))
    (nu_p (s\ par_p nil_p (out_p s c_ack nil_p))).

% Private communication inside restricted scope:
% (νx) (x<data>.0 | x(y). 0) ⟶ (νx) (0 | 0)
query succeeds ?
  reacts
    (nu_p (x\ par_p (out_p x c_data nil_p) (in_p x (_\ nil_p))))
    (nu_p (x\ par_p nil_p nil_p)).
