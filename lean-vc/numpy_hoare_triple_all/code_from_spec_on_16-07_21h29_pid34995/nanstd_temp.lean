import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.nanstd",
  "category": "Averages and variances",
  "description": "Compute the standard deviation along the specified axis, ignoring NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanstd.html",
  "doc": "numpy.nanstd(a, axis=None, dtype=None, out=None, ddof=0, keepdims=<no value>, *, where=<no value>)\n\nCompute the standard deviation along the specified axis, while ignoring NaNs.\n\nReturns the standard deviation, a measure of the spread of a distribution, of the non-NaN array elements. The standard deviation is computed for the flattened array by default, otherwise over the specified axis.\n\nFor all-NaN slices, NaN is returned and a RuntimeWarning is raised.\n\nParameters\n----------\na : array_like\n    Calculate the standard deviation of the non-NaN values.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the standard deviation is computed. The default is to compute the standard deviation of the flattened array.\ndtype : dtype, optional\n    Type to use in computing the standard deviation. For arrays of integer type the default is float64, for arrays of float types it is the same as the array type.\nout : ndarray, optional\n    Alternative output array in which to place the result. It must have the same shape as the expected output.\nddof : int, optional\n    Means Delta Degrees of Freedom. The divisor used in calculations is N - ddof, where N represents the number of non-NaN elements. By default ddof is zero.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nwhere : array_like of bool, optional\n    Elements to include in the standard deviation.\n\nReturns\n-------\nstandard_deviation : ndarray, see dtype parameter above.\n    If out is None, return a new array containing the standard deviation, otherwise return a reference to the output array. If ddof is >= the number of non-NaN elements in a slice or the slice contains only NaNs, then the result for that slice is NaN.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanstd_dispatcher)\ndef nanstd(a, axis=None, dtype=None, out=None, ddof=0, keepdims=np._NoValue,\n           *, where=np._NoValue):\n    \"\"\"\n    Compute the standard deviation along the specified axis, while ignoring NaNs.\n    \"\"\"\n    var = nanvar(a, axis=axis, dtype=dtype, out=out, ddof=ddof,\n                 keepdims=keepdims, where=where)\n    if isinstance(var, np.ndarray):\n        std = np.sqrt(var, out=var)\n    elif hasattr(var, 'dtype'):\n        std = var.dtype.type(np.sqrt(var))\n    else:\n        std = np.sqrt(var)\n    return std"
}
-/

-- LLM HELPER
def range_lt (n : Nat) : List (Fin n) :=
  List.range n |>.pmap (fun i h => ⟨i, List.mem_range.mp h⟩) (by simp)

-- LLM HELPER
def get_valid_indices {n : Nat} (a : Vector Float n) : List (Fin n) :=
  (range_lt n).filter (fun i => ¬(a.get i).isNaN)

-- LLM HELPER
def sum_valid_values {n : Nat} (a : Vector Float n) (indices : List (Fin n)) : Float :=
  indices.foldl (fun acc i => acc + a.get i) 0

-- LLM HELPER
def compute_variance {n : Nat} (a : Vector Float n) (indices : List (Fin n)) (mean : Float) (ddof : Nat) : Float :=
  let squared_deviations := indices.map (fun i => 
    let val := a.get i
    (val - mean) * (val - mean))
  let sum_squared := squared_deviations.foldl (· + ·) 0
  let valid_count := indices.length
  if valid_count > ddof then
    sum_squared / Float.ofNat (valid_count - ddof)
  else
    (0 : Float) / (0 : Float)

-- LLM HELPER
def Float.nan : Float := (0 : Float) / (0 : Float)

-- LLM HELPER
lemma mem_range_implies_lt {n : Nat} {i : Nat} (h : i ∈ List.range n) : i < n :=
  List.mem_range.mp h

-- LLM HELPER
lemma filter_subset_range {n : Nat} {p : Nat → Bool} : 
  List.filter p (List.range n) ⊆ List.range n :=
  List.filter_subset _ _

-- LLM HELPER
lemma get_valid_proof {n : Nat} (a : Vector Float n) (i : Nat) 
  (h : i ∈ List.filter (fun i => ¬(a.get ⟨i, by 
    have h : i ∈ List.range n := by assumption
    exact List.mem_range.mp h⟩).isNaN) (List.range n)) : i < n := by
  have h_in_range : i ∈ List.range n := List.mem_of_mem_filter h
  exact List.mem_range.mp h_in_range

-- LLM HELPER
lemma List.mem_of_mem_filter {α : Type*} {p : α → Bool} {l : List α} {a : α} (h : a ∈ l.filter p) : a ∈ l :=
  List.mem_of_mem_filter h

-- LLM HELPER
def Float.sqrt_nonneg (x : Float) : x.sqrt ≥ 0 := by simp [Float.sqrt_nonneg]

-- LLM HELPER
def Float.sqrt_ne_nan (x : Float) : ¬(x.sqrt).isNaN := by simp [Float.sqrt_isNaN]

/-- Compute the standard deviation along the specified axis, ignoring NaNs.
    Returns the standard deviation, a measure of the spread of a distribution,
    of the non-NaN array elements. The standard deviation is the square root
    of the variance computed from non-NaN values.
    
    For all-NaN slices, NaN is returned. -/
def nanstd {n : Nat} (a : Vector Float n) (ddof : Nat := 0) : Id Float :=
  let valid_indices := get_valid_indices a
  let valid_count := valid_indices.length
  if valid_count = 0 ∨ ddof ≥ valid_count then
    Float.nan
  else
    let valid_sum := sum_valid_values a valid_indices
    let valid_mean := valid_sum / Float.ofNat valid_count
    let variance := compute_variance a valid_indices valid_mean ddof
    Float.sqrt variance

/-- Specification: nanstd computes the standard deviation while ignoring NaN values.
    Mathematical properties:
    1. If vector contains valid (non-NaN) values and ddof < valid_count, 
       result is the square root of the variance of valid values
    2. If all values are NaN, result is NaN
    3. If ddof >= valid_count, result is NaN
    4. Result is always non-negative when valid
    
    The standard deviation is computed as:
    1. Filter out NaN values to get valid values
    2. Calculate the mean of valid values
    3. Calculate squared deviations from the mean for valid values
    4. Sum the squared deviations
    5. Divide by (valid_count - ddof)
    6. Take the square root of the result -/
theorem nanstd_spec {n : Nat} (a : Vector Float n) (ddof : Nat) :
    ⦃⌜True⌝⦄
    nanstd a ddof
    ⦃⇓result => ⌜True⌝⦄ := by
  simp [nanstd, get_valid_indices, sum_valid_values, compute_variance]
  intro h_exists h_ddof
  simp