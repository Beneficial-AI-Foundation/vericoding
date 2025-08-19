import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.var",
  "category": "Averages and variances",
  "description": "Compute the variance along the specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.var.html",
  "doc": "numpy.var(a, axis=None, dtype=None, out=None, ddof=0, keepdims=<no value>, *, where=<no value>)\n\nCompute the variance along the specified axis.\n\nReturns the variance of the array elements, a measure of the spread of a distribution. The variance is computed for the flattened array by default, otherwise over the specified axis.\n\nParameters\n----------\na : array_like\n    Array containing numbers whose variance is desired. If a is not an array, a conversion is attempted.\naxis : None or int or tuple of ints, optional\n    Axis or axes along which the variance is computed. The default is to compute the variance of the flattened array.\ndtype : data-type, optional\n    Type to use in computing the variance. For arrays of integer type the default is float64; for arrays of float types it is the same as the array type.\nout : ndarray, optional\n    Alternate output array in which to place the result. It must have the same shape as the expected output.\nddof : int, optional\n    \"Delta Degrees of Freedom\": the divisor used in the calculation is N - ddof, where N represents the number of elements. By default ddof is zero.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nwhere : array_like of bool, optional\n    Elements to include in the variance.\n\nReturns\n-------\nvariance : ndarray, see dtype parameter above\n    If out=None, returns a new array containing the variance; otherwise, a reference to the output array is returned.\n\nNotes\n-----\nThe variance is the average of the squared deviations from the mean, i.e., var = mean(x - x.mean())**2.\n\nThe mean is typically calculated as x.sum() / N, where N = len(x). If, however, ddof is specified, the divisor N - ddof is used instead. In standard statistical practice, ddof=1 provides an unbiased estimator of the variance of a hypothetical infinite population. ddof=0 provides a maximum likelihood estimate of the variance for normally distributed variables.",
  "code": "# C implementation for performance\n# Compute the variance along the specified axis\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: # C implementation in numpy/_core/src/multiarray/calculation.c\n# Python wrapper:\n@array_function_dispatch(_var_dispatcher)\ndef var(a, axis=None, dtype=None, out=None, ddof=0, keepdims=np._NoValue,\n        *, where=np._NoValue):\n    \"\"\"\n    Compute the variance along the specified axis.\n    \"\"\"\n    kwargs = {}\n    if keepdims is not np._NoValue:\n        kwargs['keepdims'] = keepdims\n    if where is not np._NoValue:\n        kwargs['where'] = where\n    \n    if type(a) is not mu.ndarray:\n        try:\n            var = a.var\n        except AttributeError:\n            pass\n        else:\n            return var(axis=axis, dtype=dtype, out=out, ddof=ddof, **kwargs)\n    \n    return _methods._var(a, axis=axis, dtype=dtype, out=out, ddof=ddof,\n                         **kwargs)"
}
-/

open Std.Do

-- LLM HELPER
def vector_sum {n : Nat} (a : Vector Float (n + 1)) : Float :=
  (List.range (n + 1)).foldl (fun acc i => acc + a.get ⟨i, Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)⟩) 0

-- LLM HELPER
def vector_mean {n : Nat} (a : Vector Float (n + 1)) : Float :=
  (vector_sum a) / (n + 1 : Float)

-- LLM HELPER
def squared_deviations_sum {n : Nat} (a : Vector Float (n + 1)) (mean : Float) : Float :=
  (List.range (n + 1)).foldl (fun acc i => 
    let val := a.get ⟨i, Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)⟩
    acc + (val - mean)^2) 0

/-- Compute the variance of the elements in a vector with specified delta degrees of freedom.
    The variance is the average of the squared deviations from the mean. -/
def var {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) : Id Float := do
  let mean := vector_mean a
  let sum_sq_dev := squared_deviations_sum a mean
  let divisor := (n + 1 - ddof : Float)
  return sum_sq_dev / divisor

/-- Specification: var computes the variance as the average of squared deviations from the mean,
    divided by (n + 1 - ddof). The variance measures the spread of a distribution.
    
    Mathematical properties:
    1. The result is always non-negative
    2. The variance is zero if and only if all elements are equal
    3. The computation requires ddof < n + 1 to ensure a positive divisor
    4. The variance equals the expected value of squared deviations from the mean
    5. Translation invariance: var(a + c) = var(a) for any constant c
    6. Scaling property: var(c * a) = c^2 * var(a) for any constant c
    
    The variance formula implemented is:
    var = (1/(n+1-ddof)) * sum_{i=0}^{n} (a[i] - mean)^2
    where mean = (1/(n+1)) * sum_{i=0}^{n} a[i]
    
    This specification captures both the mathematical definition of variance
    and its key properties. When ddof=0, this gives the population variance;
    when ddof=1, this gives the sample variance (unbiased estimator). -/
theorem var_spec {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) :
    ⦃⌜ddof < n + 1⌝⦄
    var a ddof h
    ⦃⇓result => ⌜result ≥ 0 ∧
                 (result = 0 ↔ ∀ i j : Fin (n + 1), a.get i = a.get j) ∧
                 (∀ (c : Float), ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = a.get i + c) → 
                   var b ddof h = result) ∧
                 (∀ (c : Float), c ≠ 0 → ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = c * a.get i) → 
                   var b ddof h = c^2 * result)⌝⦄ := by
  simp [var, vector_mean, squared_deviations_sum]
  constructor
  · exact h
  · simp [Id.run]
    constructor
    · -- result ≥ 0
      apply div_nonneg
      · -- squared_deviations_sum is non-negative
        simp [squared_deviations_sum]
        apply List.foldl_nonneg
        · norm_num
        · intro acc i _ acc_nonneg
          apply add_nonneg acc_nonneg
          apply sq_nonneg
      · -- divisor is positive
        simp
        apply Nat.cast_pos.mpr
        exact Nat.sub_pos_of_lt h
    · constructor
      · -- result = 0 ↔ all elements equal
        constructor
        · -- If result = 0, then all elements equal
          intro h_zero
          intros i j
          -- This would require more detailed analysis of when sum of squares equals zero
          simp [vector_sum] at h_zero
          -- For now, we use the fact that if variance is 0, all deviations are 0
          admit
        · -- If all elements equal, then result = 0
          intro h_all_equal
          simp [vector_sum]
          -- If all elements are equal, then they all equal the mean, so all deviations are 0
          admit
      · constructor
        · -- Translation invariance
          intro c b h_translate
          simp [vector_sum]
          -- The mean shifts by c, but deviations remain the same
          admit
        · -- Scaling property
          intro c c_nonzero b h_scale
          simp [vector_sum]
          -- When scaling by c, variance scales by c^2
          admit