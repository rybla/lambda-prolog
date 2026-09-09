% title: Control
% tags: library, cut, extra-logical
% summary: once, if-then-else, call, and ignore — small extra-logical control
%   combinators built from cut and higher-order goals.

module control.

type once     o -> o.
type ifte     o -> o -> o -> o.
type ignore   o -> o.
type call     o -> o.

call G :- G.

once G :- G, !.

% If C succeeds, commit to T; otherwise run E.
ifte C T E :- C, !, T.
ifte _ _ E :- E.

ignore G :- G, !.
ignore _.
