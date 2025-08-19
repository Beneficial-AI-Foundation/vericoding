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
def natToFloat : Nat → Float
  | 0 => 0.0
  | n + 1 => (natToFloat n) + 1.0

-- LLM HELPER
def problem_spec (arange_impl : {n : Nat} → Float → Float → Float → Id (Vector Float n)) 
    {n : Nat} (start stop step : Float) (h_step_nonzero : step ≠ 0) : Prop :=
    ∃ result : Vector Float n,
      arange_impl start stop step = pure result ∧
      (n = 0 → (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)) ∧
      (n > 0 → (∀ i : Fin n, result.get i = start + (natToFloat i.val) * step) ∧
               (step > 0 → start < stop ∧ ∀ i : Fin n, result.get i < stop) ∧
               (step < 0 → start > stop ∧ ∀ i : Fin n, result.get i > stop))

/-- Return evenly spaced values within a given interval [start, stop) with given step -/
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  let values := Array.range n |>.map (fun i => start + natToFloat i * step)
  pure ⟨values, by rw [Array.size_map, Array.size_range]⟩

-- LLM HELPER
lemma step_trichotomy (step : Float) (h : step ≠ 0) : step > 0 ∨ step < 0 := by
  cases' lt_trichotomy step 0 with h1 h2
  · right; exact h1
  cases' h2 with h2 h3
  · contradiction
  · left; exact h3

-- LLM HELPER
lemma vector_get_arange {n : Nat} (start stop step : Float) (i : Fin n) :
  (arange start stop step).run.get i = start + natToFloat i.val * step := by
  simp [arange, Vector.get, Array.get_map, Array.get_range]

-- LLM HELPER
lemma natToFloat_nonneg (n : Nat) : 0 ≤ natToFloat n := by
  induction n with
  | zero => simp [natToFloat]
  | succ n ih => simp [natToFloat]; linarith

theorem correctness {n : Nat} (start stop step : Float) (h_step_nonzero : step ≠ 0) :
    problem_spec arange start stop step h_step_nonzero := by
  simp [problem_spec, arange]
  use ⟨Array.range n |>.map (fun i => start + natToFloat i * step), by rw [Array.size_map, Array.size_range]⟩
  constructor
  · rfl
  constructor
  · intro h_n_zero
    cases' step_trichotomy step h_step_nonzero with h_step_pos h_step_neg
    · left
      constructor
      · exact h_step_pos
      · le_refl start
    · right  
      constructor
      · exact h_step_neg
      · le_refl start
  · intro h_n_pos
    constructor
    · intro i
      simp [Vector.get, Array.get_map, Array.get_range]
    · constructor
      · intro h_step_pos
        constructor
        · by_contra h_not_lt
          push_neg at h_not_lt
          have h_ge := h_not_lt
          have h_first : start + natToFloat 0 * step = start := by simp [natToFloat]
          have h_pos_n : 0 < n := h_n_pos
          have ⟨zero_fin⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, h_pos_n⟩, rfl⟩
          rw [h_first] at h_ge
          have h_step_pos_real : (0 : Float) < step := h_step_pos
          have h_eventually_exceeds : ∃ k : Nat, k < n ∧ start + natToFloat k * step ≥ stop := by
            use 1
            constructor
            · omega
            · simp [natToFloat]
              have h_step_pos_val : step > 0 := h_step_pos
              linarith
          obtain ⟨k, hk_lt, hk_ge⟩ := h_eventually_exceeds
          have h_contra : start + natToFloat k * step < stop := by
            have h_range_bound : ∀ i : Fin n, start + natToFloat i.val * step < stop := by
              intro i
              have h_step_pos_val : step > 0 := h_step_pos
              have h_i_bound := i.isLt
              have h_monotone : natToFloat i.val * step ≥ 0 := by
                apply mul_nonneg
                · exact natToFloat_nonneg i.val
                · linarith
              linarith
            exact h_range_bound ⟨k, hk_lt⟩
          linarith
        · intro i
          simp [Vector.get, Array.get_map, Array.get_range]
          have h_step_pos_val : step > 0 := h_step_pos
          have h_i_bound := i.isLt
          have h_monotone : natToFloat i.val * step ≥ 0 := by
            apply mul_nonneg
            · exact natToFloat_nonneg i.val
            · linarith
          have h_start_lt_stop : start < stop := by
            by_contra h_not_lt
            push_neg at h_not_lt
            have h_ge := h_not_lt
            have h_first : start + natToFloat 0 * step = start := by simp [natToFloat]
            have h_pos_n : 0 < n := h_n_pos
            have ⟨zero_fin⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, h_pos_n⟩, rfl⟩
            rw [h_first] at h_ge
            linarith
          linarith
      · intro h_step_neg
        constructor
        · by_contra h_not_gt
          push_neg at h_not_gt
          have h_le := h_not_gt
          have h_first : start + natToFloat 0 * step = start := by simp [natToFloat]
          have h_pos_n : 0 < n := h_n_pos
          have ⟨zero_fin⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, h_pos_n⟩, rfl⟩
          rw [h_first] at h_le
          have h_step_neg_real : step < (0 : Float) := h_step_neg
          have h_eventually_below : ∃ k : Nat, k < n ∧ start + natToFloat k * step ≤ stop := by
            use 1
            constructor
            · omega
            · simp [natToFloat]
              have h_step_neg_val : step < 0 := h_step_neg
              linarith
          obtain ⟨k, hk_lt, hk_le⟩ := h_eventually_below
          have h_contra : start + natToFloat k * step > stop := by
            have h_range_bound : ∀ i : Fin n, start + natToFloat i.val * step > stop := by
              intro i
              have h_step_neg_val : step < 0 := h_step_neg
              have h_i_bound := i.isLt
              have h_monotone : natToFloat i.val * step ≤ 0 := by
                apply mul_nonpos_of_nonneg_of_nonpos
                · exact natToFloat_nonneg i.val
                · linarith
              linarith
            exact h_range_bound ⟨k, hk_lt⟩
          linarith
        · intro i
          simp [Vector.get, Array.get_map, Array.get_range]
          have h_step_neg_val : step < 0 := h_step_neg
          have h_i_bound := i.isLt
          have h_monotone : natToFloat i.val * step ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos
            · exact natToFloat_nonneg i.val
            · linarith
          have h_start_gt_stop : start > stop := by
            by_contra h_not_gt
            push_neg at h_not_gt
            have h_le := h_not_gt
            have h_first : start + natToFloat 0 * step = start := by simp [natToFloat]
            have h_pos_n : 0 < n := h_n_pos
            have ⟨zero_fin⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, h_pos_n⟩, rfl⟩
            rw [h_first] at h_le
            linarith
          linarith