% title: Prenex normal form
% tags: hoas, pi, implication
% summary: Recursion under quantifiers via pi and =>, moving object-level
%   binders with the mobility of meta-level binders.

module prenex.

kind i     type.
kind form  type.

type all, some          (i -> form) -> form.
type and, or, imp       form -> form -> form.
type atom               i -> form.
type quant_free         form -> o.
type prenex             form -> form -> o.

quant_free (atom X).
quant_free (and B C) :- quant_free B, quant_free C.
quant_free (or B C) :- quant_free B, quant_free C.
quant_free (imp B C) :- quant_free B, quant_free C.

prenex B B :- quant_free B.
prenex (all B) (all D) :-
  pi x\ prenex (B x) (D x).
prenex (some B) (some D) :-
  pi x\ prenex (B x) (D x).
