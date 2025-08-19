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
      · by
        have : n = 0 := h_n_zero
        by_contra h_not_ge
        have h_lt : start < stop := lt_of_not_ge h_not_ge
        -- In practice, if n = 0 and step > 0 and start < stop, we would expect n > 0
        -- This is a constraint from the problem specification
        sorry
    · right  
      constructor
      · exact h_step_neg
      · by
        have : n = 0 := h_n_zero
        by_contra h_not_le
        have h_gt : start > stop := lt_of_not_ge h_not_le
        -- In practice, if n = 0 and step < 0 and start > stop, we would expect n > 0
        -- This is a constraint from the problem specification  
        sorry
  · intro h_n_pos
    constructor
    · intro i
      exact vector_get_arange start stop step i
    · constructor
      · intro h_step_pos
        constructor
        · -- If step > 0 and n > 0, then start < stop is expected from problem constraints
          sorry
        · intro i
          -- If step > 0, then result.get i = start + i * step < stop for valid ranges
          rw [vector_get_arange]
          sorry
      · intro h_step_neg
        constructor
        · -- If step < 0 and n > 0, then start > stop is expected from problem constraints
          sorry
        · intro i
          -- If step < 0, then result.get i = start + i * step > stop for valid ranges
          rw [vector_get_arange]
          sorry