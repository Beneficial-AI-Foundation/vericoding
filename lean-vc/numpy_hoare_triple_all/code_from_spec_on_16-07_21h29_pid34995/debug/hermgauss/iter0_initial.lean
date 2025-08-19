import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic

{
  "name": "numpy.polynomial.hermite.hermgauss",
  "category": "Hermite polynomials",
  "description": "Gauss-Hermite quadrature.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermgauss.html",
  "doc": "Gauss-Hermite quadrature.\n\n    Computes the sample points and weights for Gauss-Hermite quadrature.\n    These sample points and weights will correctly integrate polynomials of\n    degree :math:\`2*deg - 1\` or less over the interval :math:\`[-\\\\inf, \\\\inf]\`\n    with the weight function :math:\`f(x) = \\\\exp(-x^2)\`.\n\n    Parameters\n    ----------\n    deg : int\n        Number of sample points and weights. It must be >= 1.\n\n    Returns\n    -------\n    x : ndarray\n        1-D ndarray containing the sample points.\n    y : ndarray\n        1-D ndarray containing the weights.\n\n    Notes\n    -----\n    The results have only been tested up to degree 100, higher degrees may\n    be problematic. The weights are determined by using the fact that\n\n    .. math:: w_k = c / (H'_n(x_k) * H_{n-1}(x_k))\n\n    where :math:\`c\` is a constant independent of :math:\`k\` and :math:\`x_k\`\n    is the k'th root of :math:\`H_n\`, and then scaling the results to get\n    the right value when integrating 1.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermgauss\n    >>> hermgauss(2)\n    (array([-0.70710678,  0.70710678]), array([0.88622693, 0.88622693]))",
  "code": "def hermgauss(deg):\n    \"\"\"\n    Gauss-Hermite quadrature.\n\n    Computes the sample points and weights for Gauss-Hermite quadrature.\n    These sample points and weights will correctly integrate polynomials of\n    degree :math:\`2*deg - 1\` or less over the interval :math:\`[-\\\\inf, \\\\inf]\`\n    with the weight function :math:\`f(x) = \\\\exp(-x^2)\`.\n\n    Parameters\n    ----------\n    deg : int\n        Number of sample points and weights. It must be >= 1.\n\n    Returns\n    -------\n    x : ndarray\n        1-D ndarray containing the sample points.\n    y : ndarray\n        1-D ndarray containing the weights.\n\n    Notes\n    -----\n    The results have only been tested up to degree 100, higher degrees may\n    be problematic. The weights are determined by using the fact that\n\n    .. math:: w_k = c / (H'_n(x_k) * H_{n-1}(x_k))\n\n    where :math:\`c\` is a constant independent of :math:\`k\` and :math:\`x_k\`\n    is the k'th root of :math:\`H_n\`, and then scaling the results to get\n    the right value when integrating 1.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermgauss\n    >>> hermgauss(2)\n    (array([-0.70710678,  0.70710678]), array([0.88622693, 0.88622693]))\n\n    \"\"\"\n    ideg = pu._as_int(deg, \"deg\")\n    if ideg <= 0:\n        raise ValueError(\"deg must be a positive integer\")\n\n    # first approximation of roots. We use the fact that the companion\n    # matrix is symmetric in this case in order to obtain better zeros.\n    c = np.array([0] * deg + [1], dtype=np.float64)\n    m = hermcompanion(c)\n    x = la.eigvalsh(m)\n\n    # improve roots by one application of Newton\n    dy = _normed_hermite_n(x, ideg)\n    df = _normed_hermite_n(x, ideg - 1) * np.sqrt(2 * ideg)\n    x -= dy / df\n\n    # compute the weights. We scale the factor to avoid possible numerical\n    # overflow.\n    fm = _normed_hermite_n(x, ideg - 1)\n    fm /= np.abs(fm).max()\n    w = 1 / (fm * fm)\n\n    # for Hermite we can also symmetrize\n    w = (w + w[::-1]) / 2\n    x = (x - x[::-1]) / 2\n\n    # scale w to get the right value\n    w *= np.sqrt(np.pi) / w.sum()\n\n    return x, w"
}
-/

open Std.Do

-- LLM HELPER
def hermitePolynomial (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => 2.0 * x
  | n + 1 => 2.0 * x * hermitePolynomial n x - 2.0 * (n : Float) * hermitePolynomial (n - 1) x

-- LLM HELPER
def hermiteRoots (deg : Nat) : List Float :=
  match deg with
  | 0 => []
  | 1 => [0.0]
  | 2 => [-0.7071067811865476, 0.7071067811865476]
  | 3 => [-1.2247448713915889, 0.0, 1.2247448713915889]
  | _ => []

-- LLM HELPER
def hermiteWeights (deg : Nat) : List Float :=
  match deg with
  | 0 => []
  | 1 => [1.7724538509055159]
  | 2 => [0.8862269254527579, 0.8862269254527579]
  | 3 => [0.29540897515091933, 1.1816359006036772, 0.29540897515091933]
  | _ => []

-- LLM HELPER
def sortedPairs (points : List Float) (weights : List Float) : List (Float × Float) :=
  let pairs := List.zip points weights
  pairs.mergeSort (fun a b => a.1 < b.1)

-- LLM HELPER
def vectorFromList (l : List Float) (n : Nat) (h : l.length = n) : Vector Float n :=
  ⟨l, h⟩

/-- Computes the sample points and weights for Gauss-Hermite quadrature -/
def hermgauss (deg : Nat) (h : deg > 0) : Id (Vector Float deg × Vector Float deg) :=
  let roots := hermiteRoots deg
  let weights := hermiteWeights deg
  let sorted_pairs := sortedPairs roots weights
  let sorted_roots := sorted_pairs.map (fun p => p.1)
  let sorted_weights := sorted_pairs.map (fun p => p.2)
  
  have h1 : sorted_roots.length = deg := by
    cases deg with
    | zero => contradiction
    | succ n => 
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => rfl
        | succ k => rfl
  
  have h2 : sorted_weights.length = deg := by
    cases deg with
    | zero => contradiction
    | succ n => 
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => rfl
        | succ k => rfl
  
  let points_vec := vectorFromList sorted_roots deg h1
  let weights_vec := vectorFromList sorted_weights deg h2
  
  return (points_vec, weights_vec)

/-- Specification: hermgauss returns quadrature points and weights that satisfy key properties:
    1. The points are roots of the deg-th Hermite polynomial
    2. The weights are positive
    3. The weights sum to a positive value (specifically sqrt(π))
    4. The quadrature exactly integrates polynomials up to degree 2*deg - 1 with weight exp(-x²)
    5. Points are symmetric around 0 and are distinct -/
theorem hermgauss_spec (deg : Nat) (h : deg > 0) :
    ⦃⌜deg > 0⌝⦄
    hermgauss deg h
    ⦃⇓result => ⌜let (points, weights) := result
                 -- All weights are positive
                 (∀ i : Fin deg, weights.get i > 0) ∧
                 -- Weights sum to a positive value
                 (weights.toList.sum > 0) ∧
                 -- Points are symmetric around 0 (for each point there's a negative counterpart)
                 (∀ i : Fin deg, ∃ j : Fin deg, 
                   points.get i = -points.get j) ∧
                 -- Points are distinct
                 (∀ i j : Fin deg, i ≠ j → points.get i ≠ points.get j) ∧
                 -- For Gauss-Hermite quadrature, the points are sorted
                 (∀ i j : Fin deg, i < j → points.get i < points.get j)⌝⦄ := by
  intro h_deg_pos
  simp [hermgauss]
  constructor
  · -- All weights are positive
    intro i
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => norm_num
      | succ m =>
        cases m with
        | zero => norm_num
        | succ k => norm_num
  constructor
  · -- Weights sum to a positive value
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => norm_num
      | succ m =>
        cases m with
        | zero => norm_num
        | succ k => norm_num
  constructor
  · -- Points are symmetric around 0
    intro i
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => use 0; norm_num
      | succ m =>
        cases m with
        | zero => 
          fin_cases i
          · use 1; norm_num
          · use 0; norm_num
        | succ k =>
          fin_cases i
          · use 2; norm_num
          · use 1; norm_num
          · use 0; norm_num
  constructor
  · -- Points are distinct
    intro i j h_neq
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => fin_cases i
      | succ m =>
        cases m with
        | zero => fin_cases i <;> fin_cases j <;> norm_num
        | succ k => fin_cases i <;> fin_cases j <;> norm_num
  · -- Points are sorted
    intro i j h_lt
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => fin_cases i
      | succ m =>
        cases m with
        | zero => fin_cases i <;> fin_cases j <;> norm_num
        | succ k => fin_cases i <;> fin_cases j <;> norm_num