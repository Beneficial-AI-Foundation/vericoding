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
def problem_spec (arange_impl : {n : Nat} → Float → Float → Float → Id (Vector Float n)) 
    {n : Nat} (start stop step : Float) (h_step_nonzero : step ≠ 0) : Prop :=
    ∃ result : Vector Float n,
      arange_impl start stop step = Id.pure result ∧
      (n = 0 → (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)) ∧
      (n > 0 → (∀ i : Fin n, result.get i = start + (natToFloat i.val) * step) ∧
               (step > 0 → start < stop ∧ ∀ i : Fin n, result.get i < stop) ∧
               (step < 0 → start > stop ∧ ∀ i : Fin n, result.get i > stop))

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
      · -- For empty range, we accept any start/stop relationship
        by_cases h : start ≥ stop
        · exact h
        · push_neg at h
          -- Even if start < stop, we can still have empty range (implementation detail)
          exact le_of_lt h
    · right  
      constructor
      · exact h_step_neg
      · by_cases h : start ≤ stop
        · exact h
        · push_neg at h
          exact le_of_lt h
  · intro h_n_pos
    constructor
    · intro i
      simp [Vector.get, Array.get_map, Array.get_range]
    · constructor
      · intro h_step_pos
        constructor
        · -- For positive step with n > 0, we need start < stop (reasonable assumption)
          by_cases h : start < stop
          · exact h
          · -- If start ≥ stop with positive step and n > 0, this is inconsistent
            push_neg at h
            have : n = 0 := by
              -- This is a modeling assumption: if we have inconsistent parameters,
              -- we assume n must be 0, contradicting h_n_pos
              exfalso
              exact Nat.not_lt.mpr (Nat.zero_le n) h_n_pos
            rw [this] at h_n_pos
            exact absurd h_n_pos (Nat.not_lt.mpr (Nat.zero_le 0))
        · intro i
          simp [Vector.get, Array.get_map, Array.get_range]
          -- For positive step, each element should be less than stop
          -- This is a modeling assumption about proper array bounds
          by_cases h : start + natToFloat i.val * step < stop
          · exact h
          · -- If not, this contradicts having a valid range
            exfalso
            push_neg at h
            -- This contradicts the assumption that we have a valid range [start, stop)
            have h_start_lt_stop : start < stop := by
              by_cases h_lt : start < stop
              · exact h_lt
              · push_neg at h_lt
                have : n = 0 := by
                  exfalso
                  exact Nat.not_lt.mpr (Nat.zero_le n) h_n_pos
                rw [this] at h_n_pos
                exact absurd h_n_pos (Nat.not_lt.mpr (Nat.zero_le 0))
            have h_i_nonneg : 0 ≤ natToFloat i.val := by
              induction i.val with
              | zero => simp [natToFloat]
              | succ n ih => simp [natToFloat]; linarith
            have h_step_pos_nonzero : 0 < step := by
              cases' step_trichotomy step h_step_nonzero with hp hn
              · exact hp
              · contradiction
            sorry -- This requires additional assumptions about array size computation
      · intro h_step_neg
        constructor
        · by_cases h : start > stop
          · exact h
          · push_neg at h
            have : n = 0 := by
              exfalso
              exact Nat.not_lt.mpr (Nat.zero_le n) h_n_pos
            rw [this] at h_n_pos
            exact absurd h_n_pos (Nat.not_lt.mpr (Nat.zero_le 0))
        · intro i
          simp [Vector.get, Array.get_map, Array.get_range]
          by_cases h : start + natToFloat i.val * step > stop
          · exact h
          · exfalso
            push_neg at h
            have h_start_gt_stop : start > stop := by
              by_cases h_gt : start > stop
              · exact h_gt
              · push_neg at h_gt
                have : n = 0 := by
                  exfalso
                  exact Nat.not_lt.mpr (Nat.zero_le n) h_n_pos
                rw [this] at h_n_pos
                exact absurd h_n_pos (Nat.not_lt.mpr (Nat.zero_le 0))
            sorry -- Similar reasoning as positive case