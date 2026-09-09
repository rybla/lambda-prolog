% title: Lists
% tags: library, lists, horn
% summary: Standard list library — append, reverse, member, length, nth, zip,
%   permutation, and related predicates.

module lists.

kind pair  type -> type -> type.
type pr    A -> B -> pair A B.

type append      list A -> list A -> list A -> o.
type reverse     list A -> list A -> o.
type rev_aux     list A -> list A -> list A -> o.
type memb        A -> list A -> o.
type member      A -> list A -> o.
type length      list A -> int -> o.
type nth         int -> list A -> A -> o.
type last        list A -> A -> o.
type init        list A -> list A -> o.
type take        int -> list A -> list A -> o.
type drop        int -> list A -> list A -> o.
type snoc        A -> list A -> list A -> o.
type join        list A -> list A -> list A -> o.
type is_prefix   list A -> list A -> o.
type suffix      list A -> list A -> o.
type select      A -> list A -> list A -> o.
type split       list A -> list A -> list A -> o.
type zip         list A -> list B -> list (pair A B) -> o.
type unzip       list (pair A B) -> list A -> list B -> o.
type assoc       A -> B -> list (pair A B) -> o.
type domain      list (pair A B) -> list A -> o.
type range       list (pair A B) -> list B -> o.
type flatten     list (list A) -> list A -> o.
type id          list A -> list A -> o.
type same_length list A -> list B -> o.
type nextto      A -> A -> list A -> o.
type delete_all  A -> list A -> list A -> o.
type nub         list A -> list A -> o.
type permute     list A -> list A -> o.
type count       A -> list A -> int -> o.
type replicate   int -> A -> list A -> o.
type sum_list    list int -> int -> o.
type max_list    list int -> int -> o.
type min_list    list int -> int -> o.

% Structural identity of lists.
id nil nil.
id (X :: L) (X :: K) :- id L K.

same_length nil nil.
same_length (_ :: L) (_ :: K) :- same_length L K.

% Membership without cut (enumerates).
memb X (X :: L).
memb X (Y :: L) :- memb X L.

% Membership with cut (first occurrence only).
member X (X :: L) :- !.
member X (Y :: L) :- member X L.

append nil K K.
append (X :: L) K (X :: M) :- append L K M.

rev_aux nil Acc Acc.
rev_aux (X :: L) Acc K :- rev_aux L (X :: Acc) K.

reverse L K :- rev_aux L nil K.

length nil 0.
length (_ :: L) N :- length L M, N is M + 1.

nth 0 (X :: _) X.
nth N (_ :: L) Y :- N > 0, M is N - 1, nth M L Y.

last (X :: nil) X.
last (_ :: Y :: L) Z :- last (Y :: L) Z.

init (X :: nil) nil.
init (X :: Y :: L) (X :: K) :- init (Y :: L) K.

take 0 _ nil.
take N (X :: L) (X :: K) :- N > 0, M is N - 1, take M L K.

drop 0 L L.
drop N (_ :: L) K :- N > 0, M is N - 1, drop M L K.

snoc X nil (X :: nil).
snoc X (Y :: L) (Y :: K) :- snoc X L K.

% Union of lists as sets, preserving order of the first, then extras of the second.
join nil K K.
join (X :: L) K M :- memb X K, !, join L K M.
join (X :: L) K (X :: M) :- join L K M.

is_prefix nil L.
is_prefix (X :: P) (X :: L) :- is_prefix P L.

suffix S L :- append _ S L.

% select X L K  — K is L with one occurrence of X removed.
select X (X :: L) L.
select X (Y :: L) (Y :: K) :- select X L K.

split L P S :- append P S L.

nextto X Y (X :: Y :: _).
nextto X Y (_ :: L) :- nextto X Y L.

zip nil nil nil.
zip (X :: L) (Y :: K) (pr X Y :: M) :- zip L K M.

unzip nil nil nil.
unzip (pr X Y :: M) (X :: L) (Y :: K) :- unzip M L K.

assoc X Y (pr X Y :: _).
assoc X Y (_ :: L) :- assoc X Y L.

domain nil nil.
domain (pr X _ :: A) (X :: L) :- domain A L.

range nil nil.
range (pr _ Y :: A) (Y :: L) :- range A L.

flatten nil nil.
flatten (L :: Ls) K :- flatten Ls M, append L M K.

delete_all _ nil nil.
delete_all X (X :: L) K :- !, delete_all X L K.
delete_all X (Y :: L) (Y :: K) :- delete_all X L K.

nub nil nil.
nub (X :: L) (X :: K) :- delete_all X L M, nub M K.

permute nil nil.
permute L (X :: K) :- select X L M, permute M K.

count _ nil 0.
count X (X :: L) N :- !, count X L M, N is M + 1.
count X (_ :: L) N :- count X L N.

replicate 0 _ nil.
replicate N X (X :: L) :- N > 0, M is N - 1, replicate M X L.

sum_list nil 0.
sum_list (X :: L) N :- sum_list L M, N is M + X.

max_list (X :: nil) X.
max_list (X :: Y :: L) Z :- X >= Y, max_list (X :: L) Z.
max_list (X :: Y :: L) Z :- X < Y, max_list (Y :: L) Z.

min_list (X :: nil) X.
min_list (X :: Y :: L) Z :- X =< Y, min_list (X :: L) Z.
min_list (X :: Y :: L) Z :- X > Y, min_list (Y :: L) Z.
