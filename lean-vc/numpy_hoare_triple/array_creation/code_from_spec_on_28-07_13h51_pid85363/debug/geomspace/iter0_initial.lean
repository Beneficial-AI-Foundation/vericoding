import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.geomspace",
  "category": "Numerical ranges",
  "description": "Return numbers spaced evenly on a log scale (a geometric progression)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.geomspace.html",
  "doc": "\nReturn numbers spaced evenly on a log scale (a geometric progression).\n\nParameters\n----------\nstart : array_like\n    The starting value of the sequence.\nstop : array_like\n    The final value of the sequence, unless endpoint is False. In that case, num + 1 values \n    are spaced over the interval in log-space, of which all but the last (a sequence of length num) are returned.\nnum : integer, optional\n    Number of samples to generate. Default is 50.\nendpoint : boolean, optional\n    If True, stop is the last sample. Otherwise, it is not included. Default is True.\ndtype : dtype\n    The type of the output array. If dtype is not given, the data type is inferred from start and stop.\naxis : int, optional\n    The axis in the result to store the samples. Relevant only if start or stop are array-like.\n\nReturns\n-------\nsamples : ndarray\n    num samples, equally spaced on a log scale.\n\nExamples\n--------\n>>> np.geomspace(1, 1000, num=4)\narray([    1.,    10.,   100.,  1000.])\n>>> np.geomspace(1, 1000, num=3, endpoint=False)\narray([   1.,   10.,  100.])\n>>> np.geomspace(1, 1000, num=4, endpoint=False)\narray([   1.        ,    5.62341325,   31.6227766 ,  177.827941  ])\n>>> np.geomspace(1, 256, num=9)\narray([   1.,    2.,    4.,    8.,   16.,   32.,   64.,  128.,  256.])\n\nNotes\n-----\nIf the inputs or dtype are complex, the output will follow a logarithmic spiral in the complex plane.\n",
  "code": "@array_function_dispatch(_geomspace_dispatcher)\ndef geomspace(start, stop, num=50, endpoint=True, dtype=None, axis=0):\n    \"\"\"\n    Return numbers spaced evenly on a log scale (a geometric progression).\n\n    This is similar to `logspace`, but with endpoints specified directly.\n    Each output sample is a constant multiple of the previous.\n    \"\"\"\n    start = asanyarray(start)\n    stop = asanyarray(stop)\n    if _nx.any(start == 0) or _nx.any(stop == 0):\n        raise ValueError('Geometric sequence cannot include zero')\n\n    dt = result_type(start, stop, float(num), _nx.zeros((), dtype))\n    if dtype is None:\n        dtype = dt\n    else:\n        # complex to dtype('complex128') is not a downcast\n        dtype = _nx.dtype(dtype)  # Ensure dtype is a dtype object.\n\n    # Avoid negligible real or imaginary parts in output by rotating to\n    # positive real, calculating, then rotating back.\n    out_sign = _nx.sign(start)\n    if _nx.issubdtype(dt, _nx.complexfloating):\n        all_imag = (start.real == 0.) & (stop.real == 0.)\n        if _nx.any(all_imag):\n            start[all_imag] = start[all_imag].imag\n            stop[all_imag] = stop[all_imag].imag\n            out_sign[all_imag] = 1j * out_sign[all_imag]\n\n    log_start = _nx.log10(start)\n    log_stop = _nx.log10(stop)\n    result = logspace(log_start, log_stop, num=num,\n                      endpoint=endpoint, base=10.0, dtype=dtype, axis=axis)\n\n    # Make sure the endpoints match the start and stop arguments. This is\n    # necessary because np.exp(np.log(x)) is not necessarily equal to x.\n    if num > 0:\n        result[0] = start\n        if num > 1 and endpoint:\n            result[-1] = stop\n\n    result = out_sign * result\n\n    if axis != 0:\n        result = _nx.moveaxis(result, 0, axis)\n\n    return result.astype(dtype, copy=False)",
  "signature": "numpy.geomspace(start, stop, num=50, endpoint=True, dtype=None, axis=0)"
}
-/

open Std.Do

-- LLM HELPER
def pow (x : Float) (y : Float) : Float := 
  Float.exp (y * Float.log x)

/-- Return numbers spaced evenly on a log scale (a geometric progression).
    Each output sample is a constant multiple of the previous one. -/
def geomspace {n : Nat} (start stop : Float) (endpoint : Bool := true) : Id (Vector Float n) := do
  if n = 0 then
    return Vector.mk [] rfl
  else if n = 1 then
    return Vector.mk [start] rfl
  else
    let ratio : Float := 
      if endpoint then
        pow (stop / start) (1.0 / (n - 1).toFloat)
      else
        pow (stop / start) (1.0 / n.toFloat)
    
    let mut result : Array Float := #[]
    for i in [0:n] do
      let val := start * pow ratio i.toFloat
      result := result.push val
    
    -- Ensure endpoints are exact
    result := result.set! 0 start
    if endpoint && n > 1 then
      result := result.set! (n - 1) stop
    
    return ⟨result.toList, by simp [Array.toList_length]⟩

/-- Specification: geomspace returns a geometric progression from start to stop.
    - The first element is always start
    - If endpoint is true and n > 1, the last element is stop
    - All elements form a geometric progression (constant ratio between consecutive elements)
    - Neither start nor stop can be zero -/
theorem geomspace_spec {n : Nat} (start stop : Float) (endpoint : Bool)
    (h_start_nonzero : start ≠ 0) (h_stop_nonzero : stop ≠ 0) (h_n_pos : n > 0) :
    ⦃⌜start ≠ 0 ∧ stop ≠ 0 ∧ n > 0⌝⦄
    geomspace start stop endpoint
    ⦃⇓result => ⌜
      -- First element is start
      result.get ⟨0, h_n_pos⟩ = start ∧
      -- Last element is stop when endpoint is true and n > 1
      (endpoint ∧ n > 1 → result.get ⟨n - 1, Nat.sub_lt h_n_pos (Nat.zero_lt_one)⟩ = stop) ∧
      -- Geometric progression property: constant ratio between consecutive elements
      (n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
        ∀ i : Fin (n - 1),
          result.get ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = ratio * result.get ⟨i.val, Nat.lt_trans i.isLt (Nat.sub_lt h_n_pos Nat.zero_lt_one)⟩) ∧
      -- When endpoint is false, we have n values from a larger geometric sequence
      (¬endpoint ∧ n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
        ratio = pow (stop / start) (1.0 / n.toFloat) ∧
        ∀ i : Fin n,
          result.get i = start * (pow ratio i.val.toFloat))
    ⌝⦄ := by
  unfold HoareTriple
  intro h_pre
  obtain ⟨h_start_nz, h_stop_nz, h_n_pos_pre⟩ := h_pre
  simp [geomspace]
  
  -- Case analysis on n
  by_cases h_n_zero : n = 0
  · simp [h_n_zero] at h_n_pos
  
  by_cases h_n_one : n = 1
  · simp [h_n_one]
    constructor
    · simp [Vector.get, Vector.mk]
    constructor
    · intro h_endpoint_and_gt_one
      exfalso
      simp [h_n_one] at h_endpoint_and_gt_one
    constructor
    · intro h_n_ge_2
      exfalso
      simp [h_n_one] at h_n_ge_2
    · intro h_not_endpoint_and_ge_2
      exfalso
      simp [h_n_one] at h_not_endpoint_and_ge_2
  
  -- Main case: n ≥ 2
  have h_n_ge_2 : n ≥ 2 := by
    omega
  
  simp [h_n_zero, h_n_one]
  
  constructor
  · -- First element is start
    simp [Vector.get]
    
  constructor
  · -- Last element is stop when endpoint is true and n > 1
    intro h_endpoint_and_gt_one
    simp [Vector.get]
    
  constructor
  · -- Geometric progression property
    intro h_n_ge_2_hyp
    let ratio := if endpoint then pow (stop / start) (1.0 / (n - 1).toFloat)
                 else pow (stop / start) (1.0 / n.toFloat)
    use ratio
    constructor
    · -- ratio ≠ 0
      simp [ratio]
      split_ifs
      all_goals {
        apply pow_ne_zero
        · exact div_ne_zero h_stop_nz h_start_nz
      }
    · -- Geometric progression property holds
      intro i
      simp [Vector.get]
      
  · -- When endpoint is false
    intro h_not_endpoint_and_ge_2
    obtain ⟨h_not_endpoint, h_n_ge_2_final⟩ := h_not_endpoint_and_ge_2
    let ratio := pow (stop / start) (1.0 / n.toFloat)
    use ratio
    constructor
    · -- ratio ≠ 0
      apply pow_ne_zero
      exact div_ne_zero h_stop_nz h_start_nz
    constructor
    · -- ratio definition
      simp [ratio, h_not_endpoint]
    · -- All elements follow the formula
      intro i
      simp [Vector.get, h_not_endpoint]