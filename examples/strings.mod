% title: Strings
% tags: library, strings
% summary: String concatenation via @is@ and @^@, and a recogniser for the
%   empty string.

module strings.

type strcat         string -> string -> string -> o.
type empty_string   string -> o.

strcat S T U :- U is S ^ T.

empty_string "".
