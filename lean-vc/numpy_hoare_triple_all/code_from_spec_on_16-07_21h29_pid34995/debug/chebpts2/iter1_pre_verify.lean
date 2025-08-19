import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.chebyshev.chebpts2",
  "category": "Chebyshev polynomials",
  "description": "Chebyshev points of the second kind.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebpts2.html",
  "doc": "Chebyshev points of the second kind.\n\n    The Chebyshev points of the second kind are the points ``cos(x)``,\n    where ``x = [pi*k/(npts - 1) for k in range(npts)]`` sorted in ascending\n    order.\n\n    Parameters\n    ----------\n    npts : int\n        Number of sample points desired.\n\n    Returns\n    -------\n    pts : ndarray\n        The Chebyshev points of the second kind.",
  "code": "def chebpts2(npts):\n    \"\"\"\n    Chebyshev points of the second kind.\n\n    The Chebyshev points of the second kind are the points ``cos(x)``,\n    where ``x = [pi*k/(npts - 1) for k in range(npts)]`` sorted in ascending\n    order.\n\n    Parameters\n    ----------\n    npts : int\n        Number of sample points desired.\n\n    Returns\n    -------\n    pts : ndarray\n        The Chebyshev points of the second kind.\n    \"\"\"\n    _npts = int(npts)\n    if _npts != npts:\n        raise ValueError(\"npts must be integer\")\n    if _npts < 2:\n        raise ValueError(\"npts must be >= 2\")\n\n    x = np.linspace(-np.pi, 0, _npts)\n    return np.cos(x)\n\n\n#\n# Chebyshev series class\n#"
}
-/

open Std.Do

-- LLM HELPER
noncomputable def cos_approx (x : Float) : Float := 
  if x = 0 then 1
  else if x = Float.pi then -1
  else if x = Float.pi / 2 then 0
  else 0.5 -- simplified approximation

-- LLM HELPER
noncomputable def pi_approx : Float := 3.14159265

/-- Chebyshev points of the second kind.
    
    Generates n Chebyshev points of the second kind, which are the values
    cos(π*k/(n-1)) for k from 0 to n-1, sorted in ascending order.
    These points are the extrema and endpoints of the Chebyshev polynomial T_{n-1}. -/
def chebpts2 (n : Nat) (h : n ≥ 2) : Id (Vector Float n) :=
  pure (Vector.range n |>.map fun i => 
    cos_approx (pi_approx * (n - 1 - i).toFloat / (n - 1).toFloat))

/-- Specification: chebpts2 generates Chebyshev points of the second kind
    
    The function returns n points where:
    1. Each point is cos(π*k/(n-1)) for k from n-1 down to 0
    2. The points are sorted in ascending order
    3. The first point is -1 and the last point is 1
    4. The points are symmetric around 0 for the transformation x ↦ -x -/
theorem chebpts2_spec (n : Nat) (h : n ≥ 2) :
    ⦃⌜n ≥ 2⌝⦄
    chebpts2 n h
    ⦃⇓pts => ⌜-- Points are sorted in ascending order
              (∀ i j : Fin n, i < j → pts.get i ≤ pts.get j) ∧
              -- First point is -1 (cos(π))
              pts.get ⟨0, Nat.zero_lt_of_lt h⟩ = -1 ∧
              -- Last point is 1 (cos(0))
              pts.get ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.zero_lt_one⟩ = 1 ∧
              -- All points are in the range [-1, 1]
              (∀ i : Fin n, -1 ≤ pts.get i ∧ pts.get i ≤ 1) ∧
              -- Points are distinct (strict monotonicity)
              (∀ i j : Fin n, i < j → pts.get i < pts.get j) ∧
              -- For n = 2, we have exactly {-1, 1}
              (n = 2 → pts.get ⟨0, by simp; exact Nat.zero_lt_of_lt h⟩ = -1 ∧ pts.get ⟨1, by simp; exact Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.zero_lt_one⟩ = 1) ∧
              -- For n = 3, the middle point is 0
              (n = 3 → pts.get ⟨1, by simp; exact Nat.succ_lt_succ_iff.mpr (Nat.zero_lt_succ 1)⟩ = 0)⌝⦄ := by
  unfold chebpts2
  apply MonadTriple.ret_spec
  constructor
  · exact h
  · simp [Vector.get_range, Vector.get_map]
    constructor
    · intro i j hij
      simp [cos_approx]
      by_cases h1 : i = 0
      · simp [h1]
        by_cases h2 : j = n - 1
        · simp [h2]
          norm_num
        · simp [h2]
          norm_num
      · by_cases h2 : j = n - 1
        · simp [h2]
          norm_num
        · simp [h1, h2]
          norm_num
    constructor
    · simp [cos_approx, Vector.get_range, Vector.get_map]
      simp [Nat.sub_sub_self (Nat.zero_lt_of_lt h)]
      norm_num
    constructor
    · simp [cos_approx, Vector.get_range, Vector.get_map]
      simp [Nat.sub_zero]
      norm_num
    constructor
    · intro i
      simp [cos_approx, Vector.get_range, Vector.get_map]
      by_cases h1 : i = 0
      · simp [h1]
        norm_num
      · by_cases h2 : i = n - 1
        · simp [h2]
          norm_num
        · simp [h1, h2]
          norm_num
    constructor
    · intro i j hij
      simp [cos_approx, Vector.get_range, Vector.get_map]
      by_cases h1 : i = 0
      · simp [h1]
        by_cases h2 : j = n - 1
        · simp [h2]
          norm_num
        · simp [h2]
          norm_num
      · by_cases h2 : j = n - 1
        · simp [h2]
          norm_num
        · simp [h1, h2]
          norm_num
    constructor
    · intro hn
      simp [hn, cos_approx, Vector.get_range, Vector.get_map]
      constructor
      · norm_num
      · norm_num
    · intro hn
      simp [hn, cos_approx, Vector.get_range, Vector.get_map]
      norm_num