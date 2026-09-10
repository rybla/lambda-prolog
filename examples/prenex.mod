% title: Formulas and prenex form
% tags: library, hoas, pi
% summary: Object-language formulas with HOAS binders, NNF, prenex form,
%   size, occurrence, closedness, and instantiation.

module prenex.

kind i     type.
kind form  type.

type all, some             (i -> form) -> form.
type and, or, imp, iff     form -> form -> form.
type neg                   form -> form.
type tt, ff                form.
type a, b                  i.
type atom                  i -> form.
type quant_free            form -> o.
type nnf                   form -> form -> o.
type prenex                form -> form -> o.
type merge                 form -> form -> o.
type fsize                 form -> int -> o.
type occurs                i -> form -> o.
type is_closed             form -> o.
type inst                  (i -> form) -> i -> form -> o.

quant_free (atom _).
quant_free tt.
quant_free ff.
quant_free (neg B) :- quant_free B.
quant_free (and B C) :- quant_free B, quant_free C.
quant_free (or B C) :- quant_free B, quant_free C.
quant_free (imp B C) :- quant_free B, quant_free C.
quant_free (iff B C) :- quant_free B, quant_free C.

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
nnf (iff B C) (and D E) :- nnf (imp B C) D, nnf (imp C B) E.
nnf (neg (and B C)) (or D E) :- nnf (neg B) D, nnf (neg C) E.
nnf (neg (or B C)) (and D E) :- nnf (neg B) D, nnf (neg C) E.
nnf (neg (imp B C)) (and D E) :- nnf B D, nnf (neg C) E.
nnf (neg (iff B C)) F :- nnf (neg (and (imp B C) (imp C B))) F.
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
prenex (iff B C) D :- prenex B U, prenex C V, merge (iff U V) D.

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

fsize (atom _) 1.
fsize tt 1.
fsize ff 1.
fsize (neg B) N :- fsize B M, N is M + 1.
fsize (and B C) N :- fsize B I, fsize C J, N is I + J + 1.
fsize (or B C) N :- fsize B I, fsize C J, N is I + J + 1.
fsize (imp B C) N :- fsize B I, fsize C J, N is I + J + 1.
fsize (iff B C) N :- fsize B I, fsize C J, N is I + J + 1.
fsize (all B) N :- pi x\ fsize (B x) M, N is M + 1.
fsize (some B) N :- pi x\ fsize (B x) M, N is M + 1.

occurs X (atom X).
occurs X (neg B) :- occurs X B.
occurs X (and B C) :- occurs X B ; occurs X C.
occurs X (or B C) :- occurs X B ; occurs X C.
occurs X (imp B C) :- occurs X B ; occurs X C.
occurs X (iff B C) :- occurs X B ; occurs X C.
occurs X (all B) :- pi y\ occurs X (B y).
occurs X (some B) :- pi y\ occurs X (B y).

is_closed B :- pi x\ not (occurs x B).

inst B T (B T).

% ---------------------------------------------------------------------------
% Examples
%   ?- prenex (all (x\ atom x)) D.
%   ?- prenex (and (all (x\ atom x)) (atom a)) D.
%   ?- nnf (neg (and (atom a) (atom a))) D.
%   ?- nnf (neg (all (x\ atom x))) D.
%   ?- fsize (and (atom a) (atom b)) N.
%   ?- is_closed (atom a).
%   ?- pi x\ occurs x (atom x).
%   ?- inst (x\ atom x) a F.
