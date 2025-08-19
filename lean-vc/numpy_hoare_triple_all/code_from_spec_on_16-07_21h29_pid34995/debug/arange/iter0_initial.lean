import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.arange",
  "category": "Numerical ranges",
  "description": "Return evenly spaced values within a given interval",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.arange.html",
  "doc": "\nReturn evenly spaced values within a given interval.\n\nParameters\n----------\nstart : integer or real, optional\n    Start of interval. The interval includes this value. The default start value is 0.\nstop : integer or real\n    End of interval. The interval does not include this value, except in some cases where \n    step is not an integer and floating point round-off affects the length of out.\nstep : integer or real, optional\n    Spacing between values. For any output out, this is the distance between two adjacent \n    values, out[i+1] - out[i]. The default step size is 1.\ndtype : dtype, optional\n    The type of the output array. If dtype is not given, infer the data type from the \n    other input arguments.\ndevice : str, optional\n    Device on which to place the created array.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\narange : ndarray\n    Array of evenly spaced values.\n\nExamples\n--------\n>>> np.arange(3)\narray([0, 1, 2])\n>>> np.arange(3.0)\narray([ 0.,  1.,  2.])\n>>> np.arange(3,7)\narray([3, 4, 5, 6])\n>>> np.arange(3,7,2)\narray([3, 5])\n\nNotes\n-----\nWhen using a non-integer step, such as 0.1, it is often better to use numpy.linspace.\n",
  "code": "# numpy.arange is implemented in C as part of the multiarray module\n# Python signature:\n@array_function_dispatch(_arange_dispatcher)\ndef arange(start=None, stop=None, step=None, dtype=None, *, device=None, like=None):\n    \"\"\"\n    Return evenly spaced values within a given interval.\n    \"\"\"\n    # Implementation is in C - multiarray.arange\n    # Handles various input formats: arange(stop), arange(start, stop), arange(start, stop, step)\n    pass",
  "signature": "numpy.arange([start, ]stop, [step, ]dtype=None, *, device=None, like=None)"
}
-/

-- LLM HELPER
def Float.toNat (x : Float) : Nat := x.toUInt64.toNat

-- LLM HELPER
def Nat.toFloat (n : Nat) : Float := n.toUInt64.toFloat

/-- Return evenly spaced values within a given interval [start, stop) with given step -/
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  Vector.ofFn (fun i => start + i.val.toFloat * step)

/-- Specification: arange generates evenly spaced values from start to stop (exclusive) with given step.
    Each element at index i has value start + i * step, and all values are within bounds -/
theorem arange_spec {n : Nat} (start stop step : Float) 
    (h_step_nonzero : step ≠ 0) :
    ⦃⌜step ≠ 0⌝⦄
    arange start stop step
    ⦃⇓result => ⌜(n = 0 → (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)) ∧
                (n > 0 → (∀ i : Fin n, result.get i = start + (i.val.toFloat) * step) ∧
                         (step > 0 → start < stop ∧ ∀ i : Fin n, result.get i < stop) ∧
                         (step < 0 → start > stop ∧ ∀ i : Fin n, result.get i > stop))⌝⦄ := by
  unfold arange
  simp [wp_pure, wp_bind, wp_ret]
  constructor
  · intro h_n_zero
    trivial
  · intro h_n_pos
    constructor
    · intro i
      simp [Vector.get_ofFn]
    · constructor
      · intro h_step_pos
        constructor
        · by_cases h : start < stop
          · exact h
          · simp at h
            have : n = 0 := by
              by_contra h_ne
              have : n > 0 := Nat.pos_of_ne_zero h_ne
              contradiction
            rw [this] at h_n_pos
            norm_num at h_n_pos
        · intro i
          simp [Vector.get_ofFn]
          have h_i_nonneg : 0 ≤ i.val.toFloat := by
            simp [Nat.toFloat]
            exact Float.zero_le_toFloat i.val.toUInt64
          have h_step_pos_real : 0 < step := h_step_pos
          have h_product_nonneg : 0 ≤ i.val.toFloat * step := by
            apply Float.mul_nonneg h_i_nonneg
            linarith
          by_cases h : start < stop
          · have h_bound : start + i.val.toFloat * step < stop := by
              have h_i_lt : i.val.toFloat < (stop - start) / step := by
                have h_div_pos : 0 < (stop - start) / step := by
                  rw [Float.div_pos_iff]
                  left
                  constructor
                  · linarith
                  · exact h_step_pos_real
                simp [Nat.toFloat]
                have h_n_bound : n.toFloat ≤ (stop - start) / step := by
                  simp
                have h_i_bound : i.val < n := i.isLt
                have h_i_float_bound : i.val.toFloat < n.toFloat := by
                  simp [Nat.toFloat]
                  exact Float.lt_of_lt_of_le (Float.toFloat_lt_toFloat h_i_bound) (le_refl _)
                linarith
              have : start + i.val.toFloat * step = start + i.val.toFloat * step := rfl
              rw [← this]
              have : i.val.toFloat * step < stop - start := by
                rw [← Float.div_lt_iff h_step_pos_real]
                have h_i_lt : i.val.toFloat < (stop - start) / step := by
                  simp [Nat.toFloat]
                  have h_n_bound : n.toFloat ≤ (stop - start) / step := by
                    simp
                  have h_i_bound : i.val < n := i.isLt
                  have h_i_float_bound : i.val.toFloat < n.toFloat := by
                    simp [Nat.toFloat]
                    exact Float.lt_of_lt_of_le (Float.toFloat_lt_toFloat h_i_bound) (le_refl _)
                  linarith
                exact h_i_lt
              linarith
            exact h_bound
          · simp at h
            have : n = 0 := by
              by_contra h_ne
              have : n > 0 := Nat.pos_of_ne_zero h_ne
              contradiction
            rw [this] at h_n_pos
            norm_num at h_n_pos
      · intro h_step_neg
        constructor
        · by_cases h : start > stop
          · exact h
          · simp at h
            have : n = 0 := by
              by_contra h_ne
              have : n > 0 := Nat.pos_of_ne_zero h_ne
              contradiction
            rw [this] at h_n_pos
            norm_num at h_n_pos
        · intro i
          simp [Vector.get_ofFn]
          by_cases h : start > stop
          · have h_step_neg_real : step < 0 := h_step_neg
            have h_i_nonneg : 0 ≤ i.val.toFloat := by
              simp [Nat.toFloat]
              exact Float.zero_le_toFloat i.val.toUInt64
            have h_product_nonpos : i.val.toFloat * step ≤ 0 := by
              apply Float.mul_nonpos_of_nonneg_of_nonpos h_i_nonneg
              linarith
            have h_bound : start + i.val.toFloat * step > stop := by
              have : i.val.toFloat * step > (stop - start) := by
                rw [Float.lt_div_iff_mul_lt]
                · have h_i_lt : i.val.toFloat < (start - stop) / (-step) := by
                    simp [Nat.toFloat]
                    have h_n_bound : n.toFloat ≤ (start - stop) / (-step) := by
                      simp
                    have h_i_bound : i.val < n := i.isLt
                    have h_i_float_bound : i.val.toFloat < n.toFloat := by
                      simp [Nat.toFloat]
                      exact Float.lt_of_lt_of_le (Float.toFloat_lt_toFloat h_i_bound) (le_refl _)
                    linarith
                  have : -step > 0 := by linarith
                  have : i.val.toFloat * (-step) < (start - stop) := by
                    rw [Float.div_lt_iff this]
                    exact h_i_lt
                  have : -(i.val.toFloat * step) < (start - stop) := by
                    rw [← Float.neg_mul] at this
                    exact this
                  linarith
                · linarith
              linarith
            exact h_bound
          · simp at h
            have : n = 0 := by
              by_contra h_ne
              have : n > 0 := Nat.pos_of_ne_zero h_ne
              contradiction
            rw [this] at h_n_pos
            norm_num at h_n_pos