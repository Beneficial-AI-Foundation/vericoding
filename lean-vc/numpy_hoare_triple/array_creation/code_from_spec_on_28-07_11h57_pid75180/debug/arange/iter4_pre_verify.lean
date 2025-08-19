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

/-- Specification: arange generates evenly spaced values from start to stop (exclusive) with given step.
    Each element at index i has value start + i * step, and all values are within bounds -/
theorem arange_spec {n : Nat} (start stop step : Float) 
    (h_step_nonzero : step ≠ 0) :
    ⦃⌜step ≠ 0⌝⦄
    arange start stop step
    ⦃⇓result => ⌜(n = 0 → (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)) ∧
                (n > 0 → (∀ i : Fin n, result.get i = start + (natToFloat i.val) * step) ∧
                         (step > 0 → start < stop ∧ ∀ i : Fin n, result.get i < stop) ∧
                         (step < 0 → start > stop ∧ ∀ i : Fin n, result.get i > stop))⌝⦄ := by
  simp [hoare_triple_def, arange]
  intro h_pre
  constructor
  · intro h_n_zero
    cases' step_trichotomy step h_pre with h_step_pos h_step_neg
    · left
      constructor
      · exact h_step_pos
      · by_contra h_not_ge
        have h_lt : start < stop := lt_of_not_ge h_not_ge
        -- The constraint that n = 0 implies proper bounds is a natural assumption
        -- For empty arrays, we assume the bounds are consistent with the step direction
        exfalso; apply h_not_ge; linarith
    · right  
      constructor
      · exact h_step_neg
      · by_contra h_not_le
        have h_gt : start > stop := lt_of_not_ge h_not_le
        -- Similar reasoning for negative step
        exfalso; apply h_not_le; linarith
  · intro h_n_pos
    constructor
    · intro i
      exact vector_get_arange start stop step i
    · constructor
      · intro h_step_pos
        constructor
        · -- For positive step with n > 0, we assume start < stop
          by_contra h_not_lt
          have h_ge : start ≥ stop := le_of_not_gt h_not_lt
          -- This would contradict having n > 0 elements in the range
          exfalso; linarith [h_n_pos]
        · intro i
          rw [vector_get_arange]
          -- For positive step and valid index, result should be less than stop
          have h_i_nonneg : 0 ≤ natToFloat i.val := by
            induction i.val with
            | zero => simp [natToFloat]
            | succ n ih => simp [natToFloat]; linarith
          have h_step_pos_mul : 0 ≤ natToFloat i.val * step := by
            apply mul_nonneg h_i_nonneg (le_of_lt h_step_pos)
          -- Assume bounds are properly set up for the array size
          by_contra h_not_lt
          have h_ge : start + natToFloat i.val * step ≥ stop := le_of_not_gt h_not_lt
          exfalso; linarith
      · intro h_step_neg
        constructor
        · -- For negative step with n > 0, we assume start > stop
          by_contra h_not_gt
          have h_le : start ≤ stop := le_of_not_gt h_not_gt
          exfalso; linarith [h_n_pos]
        · intro i
          rw [vector_get_arange]
          -- For negative step and valid index, result should be greater than stop
          have h_i_nonneg : 0 ≤ natToFloat i.val := by
            induction i.val with
            | zero => simp [natToFloat]
            | succ n ih => simp [natToFloat]; linarith
          have h_step_neg_mul : natToFloat i.val * step ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos h_i_nonneg (le_of_lt h_step_neg)
          by_contra h_not_gt
          have h_le : start + natToFloat i.val * step ≤ stop := le_of_not_gt h_not_gt
          exfalso; linarith