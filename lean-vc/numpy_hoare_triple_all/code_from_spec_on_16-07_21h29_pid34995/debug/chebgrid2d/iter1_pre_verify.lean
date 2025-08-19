import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.chebyshev.chebgrid2d",
  "category": "Chebyshev polynomials",
  "description": "Evaluate a 2-D Chebyshev series on the Cartesian product of x and y.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebgrid2d.html",
  "doc": "Evaluate a 2-D Chebyshev series on the Cartesian product of x and y.\n\n    This function returns the values:\n\n    .. math:: p(a,b) = \\\\sum_{i,j} c_{i,j} * T_i(a) * T_j(b),\n\n    where the points \`(a, b)\` consist of all pairs formed by taking\n    \`a\` from \`x\` and \`b\` from \`y\`. The resulting points form a grid with\n    \`x\` in the first dimension and \`y\` in the second.\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars. In either\n    case, either \`x\` and \`y\` or their elements must support multiplication\n    and addition both with themselves and with the elements of \`c\`.\n\n    If \`c\` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape + y.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points in the\n        Cartesian product of \`x\` and \`y\`.  If \`x\` or \`y\` is a list or\n        tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term of\n        multi-degree i,j is contained in \`\`c[i,j]\`\`. If \`c\` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional Chebyshev series at points in the\n        Cartesian product of \`x\` and \`y\`.\n\n    See Also\n    --------\n    chebval, chebval2d, chebval3d, chebgrid3d\n    \"\"\"\n    return pu._gridnd(chebval, c, x, y)"
}
-/

open Std.Do

/-- Helper function to compute the n-th Chebyshev polynomial T_n at point x.
    T_0(x) = 1, T_1(x) = x, T_n(x) = 2x*T_{n-1}(x) - T_{n-2}(x) for n ≥ 2 -/
def chebyshevT (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 2.0 * x * chebyshevT (n + 1) x - chebyshevT n x

/-- Helper function to compute the sum of a 2D Chebyshev series at a point.
    Computes Σ_{i=0}^{rows-1} Σ_{j=0}^{cols-1} c[i,j] * T_i(x) * T_j(y) -/
def chebSeriesSum {rows cols : Nat} 
    (c : Vector (Vector Float cols) rows) 
    (x y : Float) : Float :=
  (List.range rows).foldl (fun acc i =>
    acc + (List.range cols).foldl (fun acc_j j =>
      acc_j + (c.get ⟨i, by simp; exact Nat.lt_of_mem_range _ _⟩).get ⟨j, by simp; exact Nat.lt_of_mem_range _ _⟩ * chebyshevT i x * chebyshevT j y
    ) 0.0
  ) 0.0

/-- Evaluate a 2-D Chebyshev series on the Cartesian product of x and y.
    
    This function evaluates the sum: p(a,b) = Σ_{i,j} c_{i,j} * T_i(a) * T_j(b)
    where T_i and T_j are Chebyshev polynomials of the first kind.
    The result is a 2D grid where result[k,l] = p(x[k], y[l]). -/
def chebgrid2d {nx ny rows cols : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (c : Vector (Vector Float cols) rows) : 
    Id (Vector (Vector Float ny) nx) :=
  Id.pure ⟨
    (List.range nx).map (fun i =>
      ⟨(List.range ny).map (fun j =>
        chebSeriesSum c (x.get ⟨i, by simp; exact Nat.lt_of_mem_range _ _⟩) (y.get ⟨j, by simp; exact Nat.lt_of_mem_range _ _⟩)
      ), by simp⟩
    ),
    by simp
  ⟩

-- LLM HELPER
lemma chebSeriesSum_constant {nx ny : Nat} (x : Float) (y : Float) 
    (c : Vector (Vector Float 1) 1) (h : c.get 0 = ⟨#[1.0], by simp⟩) :
    chebSeriesSum c x y = 1.0 := by
  simp [chebSeriesSum, chebyshevT]
  simp [Vector.get, h]
  simp [chebyshevT]

-- LLM HELPER
lemma vector_get_map_size {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) :
    (⟨v.val.map f, by simp⟩ : Vector β n).size = n := by
  simp [Vector.size]

-- LLM HELPER
lemma vector_get_map {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
    (⟨v.val.map f, by simp⟩ : Vector β n).get i = f (v.get i) := by
  simp [Vector.get]

/-- Specification: chebgrid2d evaluates a 2D Chebyshev series on a grid.
    
    The function computes p(x[i], y[j]) = Σ_{k,l} c[k,l] * T_k(x[i]) * T_l(y[j])
    for all combinations of x[i] and y[j], where T_k and T_l are Chebyshev 
    polynomials of the first kind. The result forms a grid with dimensions 
    nx × ny. -/
theorem chebgrid2d_spec {nx ny rows cols : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (c : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    chebgrid2d x y c
    ⦃⇓result => ⌜∀ (i : Fin nx) (j : Fin ny), 
        (result.get i).get j = chebSeriesSum c (x.get i) (y.get j)⌝⦄ := by
  simp [chebgrid2d]
  intro i j
  simp [Vector.get, List.get_map]
  simp [chebSeriesSum]

/-- Additional property: When coefficient matrix has only c[0,0] = 1 and rest are zero,
    the result is a constant grid with all values equal to 1 (since T_0(x) = 1) -/
theorem chebgrid2d_constant_case {nx ny : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (hx : nx > 0) (hy : ny > 0) :
    let c : Vector (Vector Float 1) 1 := ⟨#[⟨#[1.0], by simp⟩], by simp⟩
    ⦃⌜nx > 0 ∧ ny > 0⌝⦄
    chebgrid2d x y c
    ⦃⇓result => ⌜∀ (i : Fin nx) (j : Fin ny), 
        (result.get i).get j = 1.0⌝⦄ := by
  simp [chebgrid2d]
  intro h i j
  simp [Vector.get, List.get_map]
  have : chebSeriesSum c (x.get i) (y.get j) = 1.0 := by
    simp [chebSeriesSum, chebyshevT]
    simp [Vector.get, c]
  exact this

/-- Property: The result grid has the correct dimensions -/
theorem chebgrid2d_dimensions {nx ny rows cols : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (c : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    chebgrid2d x y c
    ⦃⇓result => ⌜result.size = nx ∧ 
        ∀ (i : Fin nx), (result.get i).size = ny⌝⦄ := by
  simp [chebgrid2d]
  constructor
  · simp [Vector.size]
  · intro i
    simp [Vector.get, List.get_map]
    simp [Vector.size]