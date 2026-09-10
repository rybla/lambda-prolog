% title: Coinduction & Bisimulation via Hypothetical Reasoning
% tags: coinduction, bisimulation, streams, greatest-fixpoint, hypothetical
% summary: Computing greatest fixpoints and verifying bisimulations on infinite
%   streams and circular state graphs using hypothetical implications (=>) as
%   coinductive hypotheses.

module coinduction.

% Infinite streams
kind stream type.
type s_cons   int -> stream -> stream.
type s_zeroes stream.
type s_ones   stream.
type s_alt01  stream.
type s_alt10  stream.

type head     stream -> int -> o.
type tail     stream -> stream -> o.

head (s_cons X _) X.
tail (s_cons _ S) S.

head s_zeroes 0.
tail s_zeroes s_zeroes.

head s_ones 1.
tail s_ones s_ones.

head s_alt01 0.
tail s_alt01 s_alt10.

head s_alt10 1.
tail s_alt10 s_alt01.

% Stream bisimulation (greatest fixpoint)
% Coinductive hypothesis stored in dynamic predicate bisim_hyp.
type bisim_hyp   stream -> stream -> o.
type bisim_check stream -> stream -> o.
type bisimilar   stream -> stream -> o.

bisimilar S1 S2 :-
  bisim_check S1 S2.

% If this pair has already been encountered on the cycle, the coinductive
% hypothesis holds: we terminate successfully.
bisim_check S1 S2 :-
  bisim_hyp S1 S2, !.

% Otherwise, we observe matching heads, step to tails, and record
% the coinductive hypothesis for this pair.
bisim_check S1 S2 :-
  head S1 X,
  head S2 X,
  tail S1 T1,
  tail S2 T2,
  (bisim_hyp S1 S2 => bisim_check T1 T2).

% Prefix extraction for stream inspection
type take_stream int -> stream -> list int -> o.
take_stream 0 _ nil.
take_stream N S (X :: Rest) :-
  N > 0,
  head S X,
  tail S Next,
  N1 is N - 1,
  take_stream N1 Next Rest.

% --- Transition System Bisimulation ---
kind state type.
type p0, p1, q0, q1, q2 state.

% Automaton P: p0 -(a)-> p1, p1 -(b)-> p0
% Automaton Q: q0 -(a)-> q1, q1 -(b)-> q2, q2 -(a)-> q1 (bisimilar to P)
type step state -> string -> state -> o.
step p0 "a" p1.
step p1 "b" p0.

step q0 "a" q1.
step q1 "b" q2.
step q2 "a" q1.

type state_bisim_hyp state -> state -> o.
type state_bisim     state -> state -> o.

state_bisim S1 S2 :-
  state_bisim_hyp S1 S2, !.

state_bisim S1 S2 :-
  (state_bisim_hyp S1 S2 => check_steps S1 S2).

type check_steps state -> state -> o.
check_steps S1 S2 :-
  % Check all transitions from S1 are matched by S2, and vice versa
  match_transitions S1 S2,
  match_transitions S2 S1.

type match_transitions state -> state -> o.
match_transitions S1 S2 :-
  step S1 Act Next1,
  step S2 Act Next2,
  state_bisim Next1 Next2.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? bisimilar s_zeroes (s_cons 0 s_zeroes).
query succeeds ? bisimilar s_alt01 (s_cons 0 (s_cons 1 s_alt01)).
query succeeds ? take_stream 4 s_alt01 L.
query succeeds ? state_bisim p0 q0.
