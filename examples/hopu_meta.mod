% title: Higher-Order Pattern Unification & Symbolic Calculus
% tags: hopu, symbolic, differentiation, simplification, higher-order
% summary: Second-order symbolic differentiation and algebraic simplification
%   exploiting higher-order patterns (Lλ) where meta-variables denote functions
%   and eigenvariables enable reasoning under binders.

module hopu_meta.

kind expr type.

% Expression constructors
type num      int -> expr.
type plus_m   expr -> expr -> expr.
type times_m  expr -> expr -> expr.
type sin_m    expr -> expr.
type cos_m    expr -> expr.

% Differentiation of single-variable functions (expr -> expr)
type diff     (expr -> expr) -> (expr -> expr) -> o.
type simp     expr -> expr -> o.
type simp_plus  expr -> expr -> expr -> o.
type simp_times expr -> expr -> expr -> o.
type simp_fun (expr -> expr) -> (expr -> expr) -> o.
type diff_and_simp (expr -> expr) -> (expr -> expr) -> o.

% Higher-order differentiation rules:
% Constant rule: C does not contain x (higher-order pattern: F x = C)
diff (x\ C) (x\ num 0).

% Identity rule: f(x) = x
diff (x\ x) (x\ num 1).

% Sum rule: d/dx (F(x) + G(x)) = F'(x) + G'(x)
diff (x\ plus_m (F x) (G x)) (x\ plus_m (DF x) (DG x)) :-
  diff F DF,
  diff G DG.

% Product rule: d/dx (F(x) * G(x)) = F'(x)*G(x) + F(x)*G'(x)
diff (x\ times_m (F x) (G x)) (x\ plus_m (times_m (DF x) (G x)) (times_m (F x) (DG x))) :-
  diff F DF,
  diff G DG.

% Chain rule for sine: d/dx sin(F(x)) = cos(F(x)) * F'(x)
diff (x\ sin_m (F x)) (x\ times_m (cos_m (F x)) (DF x)) :-
  diff F DF.

% Chain rule for cosine: d/dx cos(F(x)) = -1 * sin(F(x)) * F'(x)
diff (x\ cos_m (F x)) (x\ times_m (num (~ 1)) (times_m (sin_m (F x)) (DF x))) :-
  diff F DF.

% Algebraic simplification (bottom-up)
simp (plus_m E1 E2) R :-
  !,
  simp E1 S1,
  simp E2 S2,
  simp_plus S1 S2 R.

simp (times_m E1 E2) R :-
  !,
  simp E1 S1,
  simp E2 S2,
  simp_times S1 S2 R.

simp (sin_m E) (sin_m S) :- !, simp E S.
simp (cos_m E) (cos_m S) :- !, simp E S.
simp E E.

simp_plus (num 0) E E :- !.
simp_plus E (num 0) E :- !.
simp_plus (num A) (num B) (num C) :- !, C is A + B.
simp_plus E1 E2 (plus_m E1 E2).

simp_times (num 0) _ (num 0) :- !.
simp_times _ (num 0) (num 0) :- !.
simp_times (num 1) E E :- !.
simp_times E (num 1) E :- !.
simp_times (num A) (num B) (num C) :- !, C is A * B.
simp_times E1 E2 (times_m E1 E2).

% Simplify under a function binder using pi and sigma
simp_fun F S :-
  pi x\ sigma y\ (simp (F x) y, S x = y).

% Differentiate and simplify
diff_and_simp F SimpDF :-
  diff F RawDF,
  simp_fun RawDF SimpDF.

% ---------------------------------------------------------------------------
% Example queries:
%   ?- diff (x\ times_m (num 3) x) DF.
%   ?- diff_and_simp (x\ times_m (num 3) x) DF.
%      DF = (x\ num 3)
%   ?- diff_and_simp (x\ plus_m (times_m x x) (num 5)) DF.
%   ?- diff_and_simp (x\ sin_m (times_m (num 2) x)) DF.
