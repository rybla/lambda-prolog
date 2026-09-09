% title: Formulas and prenex form
% tags: library, hoas, pi
% summary: Object-language formulas with HOAS binders, negation-normal form,
%   and prenex normalisation that recurses under quantifiers.

module prenex.

kind i     type.
kind form  type.

type all, some             (i -> form) -> form.
type and, or, imp          form -> form -> form.
type neg                   form -> form.
type tt, ff                form.
type a                     i.
type atom                  i -> form.
type quant_free            form -> o.
type nnf                   form -> form -> o.
type prenex                form -> form -> o.
type merge                 form -> form -> o.

quant_free (atom _).
quant_free tt.
quant_free ff.
quant_free (neg B) :- quant_free B.
quant_free (and B C) :- quant_free B, quant_free C.
quant_free (or B C) :- quant_free B, quant_free C.
quant_free (imp B C) :- quant_free B, quant_free C.

nnf (atom X) (atom X).
nnf tt tt.
nnf ff ff.
nnf (neg (atom X)) (neg (atom X)).
nnf (neg tt) ff.
nnf (neg ff) tt.
nnf (neg (neg B)) C :- nnf B C.
nnf (and B C) (and D E) :- nnf B D, nnf C E.
nnf (or B C) (or D E) :- nnf B D, nnf C E.
nnf (imp B C) (or D E) :- nnf (neg B) D, nnf C E.
nnf (neg (and B C)) (or D E) :- nnf (neg B) D, nnf (neg C) E.
nnf (neg (or B C)) (and D E) :- nnf (neg B) D, nnf (neg C) E.
nnf (neg (imp B C)) (and D E) :- nnf B D, nnf (neg C) E.
nnf (all B) (all D) :- pi x\ nnf (B x) (D x).
nnf (some B) (some D) :- pi x\ nnf (B x) (D x).
nnf (neg (all B)) (some D) :- pi x\ nnf (neg (B x)) (D x).
nnf (neg (some B)) (all D) :- pi x\ nnf (neg (B x)) (D x).

prenex B B :- quant_free B, !.
prenex (all B) (all D) :- pi x\ prenex (B x) (D x).
prenex (some B) (some D) :- pi x\ prenex (B x) (D x).
prenex (neg B) D :- nnf (neg B) C, prenex C D.
prenex (and B C) D :- prenex B U, prenex C V, merge (and U V) D.
prenex (or B C) D :- prenex B U, prenex C V, merge (or U V) D.
prenex (imp B C) D :- prenex B U, prenex C V, merge (imp U V) D.

merge (and (all B) C) (all D) :- pi x\ merge (and (B x) C) (D x).
merge (and B (all C)) (all D) :- pi x\ merge (and B (C x)) (D x).
merge (and (some B) C) (some D) :- pi x\ merge (and (B x) C) (D x).
merge (and B (some C)) (some D) :- pi x\ merge (and B (C x)) (D x).
merge (or (all B) C) (all D) :- pi x\ merge (or (B x) C) (D x).
merge (or B (all C)) (all D) :- pi x\ merge (or B (C x)) (D x).
merge (or (some B) C) (some D) :- pi x\ merge (or (B x) C) (D x).
merge (or B (some C)) (some D) :- pi x\ merge (or B (C x)) (D x).
merge (imp (all B) C) (some D) :- pi x\ merge (imp (B x) C) (D x).
merge (imp (some B) C) (all D) :- pi x\ merge (imp (B x) C) (D x).
merge (imp B (all C)) (all D) :- pi x\ merge (imp B (C x)) (D x).
merge (imp B (some C)) (some D) :- pi x\ merge (imp B (C x)) (D x).
merge B B :- quant_free B.
