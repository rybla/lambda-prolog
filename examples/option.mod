% title: Options
% tags: library, datatypes
% summary: The option type — none / some — with map, default, and conversion
%   from a succeeding goal.

module option.

kind option      type -> type.
type none        option A.
type some        A -> option A.

type is_none     option A -> o.
type is_some     option A -> A -> o.
type from_option A -> option A -> A -> o.
type map_option  (A -> B) -> option A -> option B -> o.
type map_option_pred (A -> B -> o) -> option A -> option B -> o.
type filter_option   (A -> o) -> option A -> option A -> o.
type and_then_option (A -> option B -> o) -> option A -> option B -> o.
type or_else_option  option A -> option A -> option A -> o.
type to_list         option A -> list A -> o.
type from_list_first list A -> option A -> o.
type option_of   (A -> o) -> A -> option A -> o.
type flatten_option option (option A) -> option A -> o.
type cat_options    list (option A) -> list A -> o.
type option_all     (A -> o) -> option A -> o.

is_none none.

is_some (some X) X.

from_option D none D.
from_option _ (some X) X.

map_option _ none none.
map_option F (some X) (some (F X)).

map_option_pred _ none none.
map_option_pred P (some X) (some Y) :- P X Y.

filter_option _ none none.
filter_option P (some X) (some X) :- P X, !.
filter_option _ (some _) none.

and_then_option _ none none.
and_then_option F (some X) R :- F X R.

or_else_option (some X) _ (some X).
or_else_option none Opt Opt.

to_list none nil.
to_list (some X) (X :: nil).

from_list_first nil none.
from_list_first (X :: _) (some X).

% If G X succeeds, wrap the first binding; otherwise none.
option_of G X (some X) :- G X, !.
option_of _ _ none.

flatten_option none none.
flatten_option (some Opt) Opt.

cat_options nil nil.
cat_options (none :: Rest) Out :- cat_options Rest Out.
cat_options (some X :: Rest) (X :: Out) :- cat_options Rest Out.

option_all _ none.
option_all P (some X) :- P X.

query succeeds ? is_none none.
query succeeds ? is_some (some 3) X.
query succeeds ? from_option 0 none Y.
query succeeds ? from_option 0 (some 4) Y.
query succeeds ? map_option (x\ x) (some 1) R.
query succeeds ? filter_option (x\ x > 2) (some 3) R.
query succeeds ? filter_option (x\ x > 2) (some 1) R.
query succeeds ? or_else_option none (some 5) R.
query succeeds ? to_list (some 7) L.
query succeeds ? from_list_first (1 :: 2 :: nil) R.
query succeeds ? option_of (x\ x = 2) X R.
