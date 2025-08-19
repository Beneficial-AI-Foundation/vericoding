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
def Float.pow (x : Float) (y : Float) : Float := x ^ y

-- LLM HELPER
def Vector.ofFn {α : Type*} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨List.ofFn f, List.length_ofFn f⟩

/-- Return numbers spaced evenly on a log scale (a geometric progression).
    Each output sample is a constant multiple of the previous one. -/
def geomspace {n : Nat} (start stop : Float) (endpoint : Bool := true) : Id (Vector Float n) := do
  if n = 0 then
    return Vector.ofFn (fun _ => 0)
  else if n = 1 then
    return Vector.ofFn (fun _ => start)
  else
    let ratio : Float := 
      if endpoint then
        (stop / start).pow (1.0 / (n - 1).toFloat)
      else
        (stop / start).pow (1.0 / n.toFloat)
    
    let result := Vector.ofFn (fun i : Fin n => start * ratio.pow i.val.toFloat)
    
    -- Ensure exact endpoints when endpoint is True
    if endpoint then
      let corrected := Vector.ofFn (fun i : Fin n => 
        if i.val = 0 then start
        else if i.val = n - 1 then stop
        else start * ratio.pow i.val.toFloat)
      return corrected
    else
      return result

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
        ratio = (stop / start) ^ (1.0 / n.toFloat) ∧
        ∀ i : Fin n,
          result.get i = start * (ratio ^ i.val.toFloat))
    ⌝⦄ := by
  unfold geomspace
  simp only [Id.bind_eq, Id.pure_eq, Id.run]
  split
  · -- n = 0 case - contradiction with h_n_pos
    omega
  · split
    · -- n = 1 case
      simp [Vector.ofFn, Vector.get]
      constructor
      · -- First element is start
        simp [List.get_ofFn]
      constructor
      · -- Last element when endpoint is true (vacuous since n = 1)
        intro h_endpoint h_n_gt_1
        omega
      constructor
      · -- Geometric progression (vacuous since n < 2)
        intro h_n_ge_2
        omega
      · -- Endpoint false case (vacuous since n < 2)
        intro h_not_endpoint h_n_ge_2
        omega
    · -- n > 1 case
      split <;> 
      { simp [Vector.ofFn, Vector.get, List.get_ofFn]
        constructor
        · -- First element is start
          by_cases h_eq : endpoint
          · simp [h_eq]
          · simp [h_eq]
        constructor
        · -- Last element when endpoint is true
          intro h_endpoint h_n_gt_1
          simp [h_endpoint]
        constructor
        · -- Geometric progression property
          intro h_n_ge_2
          by_cases h_eq : endpoint
          · -- endpoint case
            simp [h_eq]
            use (stop / start).pow (1.0 / (n - 1).toFloat)
            constructor
            · -- ratio ≠ 0
              apply pow_ne_zero
              exact div_ne_zero h_stop_nonzero h_start_nonzero
            · -- ratio property for interior points
              intro i
              by_cases h1 : i.val = 0
              · simp [h1]
                ring
              by_cases h2 : i.val + 1 = n - 1
              · simp [h2]
                field_simp
                ring
              · simp [h1, h2]
                ring
          · -- not endpoint case  
            simp [h_eq]
            use (stop / start).pow (1.0 / n.toFloat)
            constructor
            · apply pow_ne_zero
              exact div_ne_zero h_stop_nonzero h_start_nonzero
            · intro i
              ring
        · -- Endpoint false case
          intro h_not_endpoint h_n_ge_2
          simp [h_not_endpoint]
          use (stop / start).pow (1.0 / n.toFloat)
          constructor
          · apply pow_ne_zero
            exact div_ne_zero h_stop_nonzero h_start_nonzero
          constructor
          · rfl
          · intro i
            rfl }