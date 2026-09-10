% title: Control
% tags: library, cut, extra-logical
% summary: once, if-then-else, call, ignore, unless, and bounded repeat —
%   extra-logical control combinators built from cut and higher-order goals.

module control.

type once      o -> o.
type ifte      o -> o -> o -> o.
type ignore    o -> o.
type call      o -> o.
type unless    o -> o -> o.
type repeat_n  int -> o -> o.
type and_then  o -> o -> o.
type or_else   o -> o -> o.

call G :- G.

and_then A B :- A, B.

or_else A B :- A ; B.

once G :- G, !.

% If C succeeds, commit to T; otherwise run E.
ifte C T E :- C, !, T.
ifte _ _ E :- E.

% unless C G  runs G only when C fails.
unless C G :- C, !, fail.
unless _ G :- G.

ignore G :- G, !.
ignore _.

% repeat_n N G  succeeds if G succeeds N times in a row (G may bind).
repeat_n 0 _.
repeat_n N G :- N > 0, G, M is N - 1, repeat_n M G.

% ---------------------------------------------------------------------------
% Example queries
query succeeds ? once true.
query succeeds ? once (true, true).
query fails ? once (fail, true).
query succeeds ? ifte true true fail.
query succeeds ? ifte fail fail true.
query succeeds ? ignore fail.
query succeeds ? unless fail true.
query fails ? unless true fail.
query succeeds ? call (true ; fail).
query succeeds ? repeat_n 3 true.
