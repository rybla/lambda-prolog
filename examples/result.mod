% title: Result & Either Standard Library
% tags: result, either, library, stdlib, error-handling
% summary: Standard library module for Result/Either types: ok and err
%   constructors, monadic bind (and_then), functor mapping (map_ok, map_err),
%   safe unwrapping, list partitioning, and sequence aggregation.

module result.

kind res type -> type -> type.

type ok  A -> res A B.
type err B -> res A B.

type is_ok             res A B -> o.
type is_err            res A B -> o.
type unwrap            res A B -> A -> o.
type unwrap_or         A -> res A B -> A -> o.
type map_ok            (A -> C -> o) -> res A B -> res C B -> o.
type map_err           (B -> D -> o) -> res A B -> res A D -> o.
type and_then          (A -> res C B -> o) -> res A B -> res C B -> o.
type or_else           (B -> res A D -> o) -> res A B -> res A D -> o.
type bifold            (A -> C -> o) -> (B -> C -> o) -> res A B -> C -> o.
type partition_results list (res A B) -> list A -> list B -> o.
type sequence_results  list (res A B) -> res (list A) B -> o.

% Status tests
is_ok (ok _).
is_err (err _).

% Unwrapping
unwrap (ok X) X.

unwrap_or _ (ok X) X.
unwrap_or Def (err _) Def.

% Functor mapping
map_ok F (ok X) (ok Y) :-
  F X Y.
map_ok _ (err E) (err E).

map_err _ (ok X) (ok X).
map_err G (err E) (err E2) :-
  G E E2.

% Monadic bind / and_then
and_then F (ok X) Res :-
  F X Res.
and_then _ (err E) (err E).

% Fallback / or_else
or_else _ (ok X) (ok X).
or_else G (err E) Res :-
  G E Res.

% Fold over both variants
bifold F _ (ok X) Res :-
  F X Res.
bifold _ G (err E) Res :-
  G E Res.

% Partition a list of results into successes and failures
partition_results nil nil nil.
partition_results (ok X :: Rest) (X :: Oks) Errs :-
  partition_results Rest Oks Errs.
partition_results (err E :: Rest) Oks (E :: Errs) :-
  partition_results Rest Oks Errs.

% Sequence a list of results: aborts on first err, or collects all oks
sequence_results nil (ok nil).
sequence_results (err E :: _) (err E).
sequence_results (ok X :: Rest) Res :-
  sequence_results Rest RestRes,
  seq_combine X RestRes Res.

type seq_combine A -> res (list A) B -> res (list A) B -> o.
seq_combine X (ok Xs) (ok (X :: Xs)).
seq_combine _ (err E) (err E).

% ---------------------------------------------------------------------------
% Example queries:
%   ?- map_ok (x\ y\ y is x + 1) (ok 5) R.
%      R = ok 6
%   ?- and_then (x\ r\ r = ok (x * 2)) (ok 10) R.
%      R = ok 20
%   ?- partition_results (ok 1 :: err "fail" :: ok 3 :: nil) Oks Errs.
%      Oks = 1 :: 3 :: nil, Errs = "fail" :: nil
%   ?- sequence_results (ok 1 :: ok 2 :: nil) R.
%      R = ok (1 :: 2 :: nil)
