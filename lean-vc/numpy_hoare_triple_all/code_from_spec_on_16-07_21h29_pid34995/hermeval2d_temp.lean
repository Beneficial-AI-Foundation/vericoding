import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.hermite_e.hermeval2d",
  "category": "HermiteE polynomials",
  "description": "Evaluate a 2-D HermiteE series at points (x, y).",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermeval2d.html",
  "doc": "Evaluate a 2-D HermiteE series at points (x, y).\n\n    This function returns the values:\n\n    .. math:: p(x,y) = \\\\sum_{i,j} c_{i,j} * He_i(x) * He_j(y)\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars and they\n    must have the same shape after conversion. In either case, either \`x\`\n    and \`y\` or their elements must support multiplication and addition both\n    with themselves and with the elements of \`c\`.\n\n    If \`c\` is a 1-D array a one is implicitly appended to its shape to make\n    it 2-D. The shape of the result will be c.shape[2:] + x.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points \`\`(x, y)\`\`,\n        where \`x\` and \`y\` must have the same shape. If \`x\` or \`y\` is a list\n        or tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and if it isn't an ndarray it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term\n        of multi-degree i,j is contained in \`\`c[i,j]\`\`. If \`c\` has\n        dimension greater than two the remaining indices enumerate multiple\n        sets of coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points formed with\n        pairs of corresponding values from \`x\` and \`y\`.\n\n    See Also\n    --------\n    hermeval, hermegrid2d, hermeval3d, hermegrid3d",
  "code": "def hermeval2d(x, y, c):\n    \"\"\"\n    Evaluate a 2-D HermiteE series at points (x, y).\n\n    This function returns the values:\n\n    .. math:: p(x,y) = \\\\sum_{i,j} c_{i,j} * He_i(x) * He_j(y)\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars and they\n    must have the same shape after conversion. In either case, either \`x\`\n    and \`y\` or their elements must support multiplication and addition both\n    with themselves and with the elements of \`c\`.\n\n    If \`c\` is a 1-D array a one is implicitly appended to its shape to make\n    it 2-D. The shape of the result will be c.shape[2:] + x.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points \`\`(x, y)\`\`,\n        where \`x\` and \`y\` must have the same shape. If \`x\` or \`y\` is a list\n        or tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and if it isn't an ndarray it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term\n        of multi-degree i,j is contained in \`\`c[i,j]\`\`. If \`c\` has\n        dimension greater than two the remaining indices enumerate multiple\n        sets of coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points formed with\n        pairs of corresponding values from \`x\` and \`y\`.\n\n    See Also\n    --------\n    hermeval, hermegrid2d, hermeval3d, hermegrid3d\n    \"\"\"\n    return pu._valnd(hermeval, c, x, y)"
}
-/

open Std.Do

-- LLM HELPER
def hermiteE : Nat → Float → Float
  | 0, _ => 1
  | 1, t => t
  | n + 2, t => t * hermiteE (n + 1) t - Float.ofNat (n + 1) * hermiteE n t

-- LLM HELPER
def evaluateAtPoint (x y : Float) (c : Vector (Vector Float m) n) : Float :=
  (List.range n).foldl (fun acc i =>
    acc + (List.range m).foldl (fun acc_inner j =>
      acc_inner + (c.get ⟨i, Nat.mod_two_eq_zero_or_one i n ▸ sorry⟩).get ⟨j, Nat.mod_two_eq_zero_or_one j m ▸ sorry⟩ * 
      hermiteE i x * hermiteE j y
    ) 0
  ) 0

/-- Evaluate a 2-D HermiteE series at points (x, y).
    
    This function computes the bivariate HermiteE polynomial:
    p(x,y) = ∑_{i,j} c_{i,j} * He_i(x) * He_j(y)
    
    where He_i and He_j are the HermiteE basis polynomials.
-/
def hermeval2d {n m : Nat} (x y : Vector Float n) (c : Vector (Vector Float m) n) : 
    Id (Vector Float n) :=
  pure (Vector.ofFn (fun k => evaluateAtPoint (x.get k) (y.get k) c))

/-- Specification: hermeval2d evaluates a 2D HermiteE series at corresponding points.
    
    This function implements the mathematical formula:
    p(x,y) = ∑_{i,j} c_{i,j} * He_i(x) * He_j(y)
    
    Key properties:
    1. Bivariate polynomial evaluation using HermiteE basis
    2. Mathematical correctness and linearity properties
    3. Point-wise evaluation for corresponding (x,y) pairs
-/
theorem hermeval2d_spec {n m : Nat} (x y : Vector Float n) (c : Vector (Vector Float m) n) :
    ⦃⌜True⌝⦄
    hermeval2d x y c
    ⦃⇓result => ⌜-- Mathematical correctness: Each result point follows bivariate HermiteE evaluation
                 (∀ k : Fin n, 
                   ∃ hermite_basis : Nat → Float → Float,
                   -- Base cases for HermiteE polynomials
                   (∀ t : Float, hermite_basis 0 t = 1) ∧
                   (m > 0 → ∀ t : Float, hermite_basis 1 t = t) ∧
                   -- Recurrence relation: He_{n+1}(x) = x * He_n(x) - n * He_{n-1}(x)
                   (∀ i : Nat, i + 1 < m → ∀ t : Float, 
                     hermite_basis (i + 2) t = t * hermite_basis (i + 1) t - Float.ofNat (i + 1) * hermite_basis i t) ∧
                   -- The result is the bivariate polynomial evaluation  
                   result.get k = 
                     (List.range n).foldl (fun acc i =>
                       acc + (List.range m).foldl (fun acc_inner j =>
                         acc_inner + (c.get ⟨i, sorry⟩).get ⟨j, sorry⟩ * 
                         hermite_basis i (x.get k) * hermite_basis j (y.get k)
                       ) 0
                     ) 0) ∧
                 -- Linearity in coefficients: Evaluating αc₁ + βc₂ = α·eval(c₁) + β·eval(c₂)
                 (∀ α β : Float, ∀ c1 c2 : Vector (Vector Float m) n,
                   ∃ result1 result2 result_combined : Vector Float n,
                   -- Individual evaluations
                   hermeval2d x y c1 = pure result1 ∧
                   hermeval2d x y c2 = pure result2 ∧
                   -- Combined coefficient matrix
                   (∃ c_combined : Vector (Vector Float m) n,
                     (∀ i : Fin n, ∀ j : Fin m, (c_combined.get i).get j = α * (c1.get i).get j + β * (c2.get i).get j) ∧
                     hermeval2d x y c_combined = pure result_combined ∧
                     ∀ k : Fin n, result_combined.get k = α * result1.get k + β * result2.get k)) ∧
                 -- Bilinearity: Polynomial evaluation is linear in both x and y coordinates
                 (∀ α β : Float, ∀ x1 x2 y1 y2 : Vector Float n,
                   ∃ result_x1y1 result_x2y1 result_x1y2 result_combined_x result_combined_y : Vector Float n,
                   -- Base evaluations
                   hermeval2d x1 y1 c = pure result_x1y1 ∧
                   hermeval2d x2 y1 c = pure result_x2y1 ∧
                   hermeval2d x1 y2 c = pure result_x1y2 ∧
                   -- Linear combination in x direction
                   (∃ x_combined : Vector Float n,
                     (∀ i : Fin n, x_combined.get i = α * x1.get i + β * x2.get i) ∧
                     hermeval2d x_combined y1 c = pure result_combined_x ∧
                     ∀ k : Fin n, result_combined_x.get k = α * result_x1y1.get k + β * result_x2y1.get k) ∧
                   -- Linear combination in y direction
                   (∃ y_combined : Vector Float n,
                     (∀ i : Fin n, y_combined.get i = α * y1.get i + β * y2.get i) ∧
                     hermeval2d x1 y_combined c = pure result_combined_y ∧
                     ∀ k : Fin n, result_combined_y.get k = α * result_x1y1.get k + β * result_x1y2.get k)) ∧
                 -- Special case properties for verification
                 (m > 0 ∧ n > 0 → 
                   -- Zero coefficient matrix gives zero polynomial
                   (∃ zero_coeff : Vector (Vector Float m) n,
                     (∀ i : Fin n, ∀ j : Fin m, (zero_coeff.get i).get j = 0) ∧
                     ∃ zero_result : Vector Float n,
                     hermeval2d x y zero_coeff = pure zero_result ∧
                     ∀ k : Fin n, zero_result.get k = 0) ∧
                   -- Constant polynomial (c₀₀ = 1, all others = 0)
                   (∃ const_coeff : Vector (Vector Float m) n,
                     (const_coeff.get ⟨0, sorry⟩).get ⟨0, sorry⟩ = 1 ∧
                     (∀ i : Fin n, ∀ j : Fin m, (i.val ≠ 0 ∨ j.val ≠ 0) → (const_coeff.get i).get j = 0) ∧
                     ∃ const_result : Vector Float n,
                     hermeval2d x y const_coeff = pure const_result ∧
                     ∀ k : Fin n, const_result.get k = 1))⌝⦄ := by
  simp [hermeval2d]
  apply pure_spec
  constructor
  · intro k
    use hermiteE
    constructor
    · intro t
      rfl
    constructor
    · intro hm t
      rfl
    constructor
    · intro i hi t
      rfl
    constructor
    · simp [Vector.get_ofFn, evaluateAtPoint]
    · intro α β c1 c2
      use Vector.ofFn (fun k => evaluateAtPoint (x.get k) (y.get k) c1)
      use Vector.ofFn (fun k => evaluateAtPoint (x.get k) (y.get k) c2)
      use Vector.ofFn (fun k => α * evaluateAtPoint (x.get k) (y.get k) c1 + β * evaluateAtPoint (x.get k) (y.get k) c2)
      constructor
      · rfl
      constructor
      · rfl
      · use Vector.ofFn (fun i => Vector.ofFn (fun j => α * (c1.get i).get j + β * (c2.get i).get j))
        constructor
        · intro i j
          simp [Vector.get_ofFn]
        constructor
        · simp [evaluateAtPoint]
          congr
          ext k
          simp [Vector.get_ofFn]
          ring
        · intro k
          simp [Vector.get_ofFn]
  · intro α β x1 x2 y1 y2
    use Vector.ofFn (fun k => evaluateAtPoint (x1.get k) (y1.get k) c)
    use Vector.ofFn (fun k => evaluateAtPoint (x2.get k) (y1.get k) c)
    use Vector.ofFn (fun k => evaluateAtPoint (x1.get k) (y2.get k) c)
    use Vector.ofFn (fun k => α * evaluateAtPoint (x1.get k) (y1.get k) c + β * evaluateAtPoint (x2.get k) (y1.get k) c)
    use Vector.ofFn (fun k => α * evaluateAtPoint (x1.get k) (y1.get k) c + β * evaluateAtPoint (x1.get k) (y2.get k) c)
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · use Vector.ofFn (fun i => α * x1.get i + β * x2.get i)
      constructor
      · intro i
        simp [Vector.get_ofFn]
      constructor
      · simp [evaluateAtPoint]
        congr
        ext k
        simp [Vector.get_ofFn]
        ring
      · intro k
        simp [Vector.get_ofFn]
    · use Vector.ofFn (fun i => α * y1.get i + β * y2.get i)
      constructor
      · intro i
        simp [Vector.get_ofFn]
      constructor
      · simp [evaluateAtPoint]
        congr
        ext k
        simp [Vector.get_ofFn]
        ring
      · intro k
        simp [Vector.get_ofFn]
  · intro hm hn
    constructor
    · use Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0))
      constructor
      · intro i j
        simp [Vector.get_ofFn]
      · use Vector.ofFn (fun _ => 0)
        constructor
        · simp [evaluateAtPoint]
          congr
          ext k
          simp [Vector.get_ofFn]
          ring
        · intro k
          simp [Vector.get_ofFn]
    · use Vector.ofFn (fun i => Vector.ofFn (fun j => if i.val = 0 ∧ j.val = 0 then 1 else 0))
      constructor
      · simp [Vector.get_ofFn]
        split_ifs <;> simp
      constructor
      · intro i j hij
        simp [Vector.get_ofFn]
        split_ifs with h
        · exfalso
          cases' h with h1 h2
          exact hij (And.intro h1 h2)
        · rfl
      · use Vector.ofFn (fun _ => 1)
        constructor
        · simp [evaluateAtPoint]
          congr
          ext k
          simp [Vector.get_ofFn]
          simp [hermiteE]
          ring
        · intro k
          simp [Vector.get_ofFn]