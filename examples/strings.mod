% title: Strings & String Operations
% tags: library, strings, builtins, standard-library
% summary: String concatenation, list joining with delimiters, recognition of
%   empty strings, and evaluable string expressions using the built-in string
%   concatenation operator (^) and arithmetic/string evaluator (is).

module strings.

accumulate lists.

% ============================================================================
% Predicate Signatures
% ============================================================================

type strcat         string -> string -> string -> o.
type concat_all     list string -> string -> o.
type empty_string   string -> o.
type join_with      string -> list string -> string -> o.

% ============================================================================
% Implementation
% ============================================================================

% Concatenate two strings S and T into U using the built-in infix operator (^).
% The 'is' connective evaluates ground string expressions:
strcat S T U :- U is S ^ T.

% Recognizer for empty strings:
empty_string "".

% Fold-style concatenation: folds a list of strings into a single string.
concat_all nil "".
concat_all (S :: L) U :-
  concat_all L T,
  U is S ^ T.

% Intercalate a separator between elements of a string list:
% Base case: empty list produces empty string.
join_with _ nil "".
% Single element: returns the string itself without separator.
join_with _ (S :: nil) S.
% Recursive case: joins the tail with separator, then prepends head + separator.
join_with Sep (S :: T :: L) U :-
  join_with Sep (T :: L) V,
  W is S ^ Sep,
  U is W ^ V.

% ============================================================================
% Example Queries
% ============================================================================

query succeeds ? strcat "ab" "cd" S.
query succeeds ? empty_string "".
query succeeds ? concat_all ("a" :: "b" :: "c" :: nil) S.
query succeeds ? join_with "," ("a" :: "b" :: "c" :: nil) S.
query succeeds ? S is "hello" ^ " " ^ "world".
