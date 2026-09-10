% title: Strings
% tags: library, strings
% summary: String concatenation via @is@ and @^@, joining a list of strings,
%   and a few recognisers.

module strings.

accumulate lists.

type strcat         string -> string -> string -> o.
type concat_all     list string -> string -> o.
type empty_string   string -> o.
type join_with      string -> list string -> string -> o.

strcat S T U :- U is S ^ T.

empty_string "".

concat_all nil "".
concat_all (S :: L) U :- concat_all L T, U is S ^ T.

join_with _ nil "".
join_with _ (S :: nil) S.
join_with Sep (S :: T :: L) U :-
  join_with Sep (T :: L) V,
  W is S ^ Sep,
  U is W ^ V.

query succeeds ? strcat "ab" "cd" S.
query succeeds ? empty_string "".
query succeeds ? concat_all ("a" :: "b" :: "c" :: nil) S.
query succeeds ? join_with "," ("a" :: "b" :: "c" :: nil) S.
query succeeds ? S is "hello" ^ " " ^ "world".
