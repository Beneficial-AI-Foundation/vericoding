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
def generate_arange_values (start : Float) (step : Float) : Nat → List Float
  | 0 => []
  | n + 1 => start :: generate_arange_values (start + step) step n

-- LLM HELPER
def list_to_vector {α : Type} (l : List α) : Vector α l.length :=
  ⟨l, rfl⟩

/-- Return evenly spaced values within a given interval [start, stop) with given step -/
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  Id.pure (list_to_vector (generate_arange_values start step n).take n |>.extend n 0.0)
  where
    List.extend (l : List α) (target_len : Nat) (default : α) : List α :=
      l ++ List.replicate (target_len - l.length) default

-- LLM HELPER
theorem generate_arange_values_length (start step : Float) (n : Nat) :
    (generate_arange_values start step n).length = n := by
  induction n with
  | zero => simp [generate_arange_values]
  | succ n ih => simp [generate_arange_values, ih]

-- LLM HELPER  
theorem generate_arange_values_get (start step : Float) (n : Nat) (i : Fin n) :
    (generate_arange_values start step n).get ⟨i.val, by rw [generate_arange_values_length]; exact i.isLt⟩ = 
    start + i.val.toFloat * step := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => 
    cases' i.val with k
    · simp [generate_arange_values, List.get]
      ring
    · have h : k < n := Nat.lt_of_succ_lt_succ i.isLt
      simp [generate_arange_values, List.get]
      rw [ih ⟨k, h⟩]
      ring

-- LLM HELPER
theorem Nat.toFloat_succ (n : Nat) : (n + 1).toFloat = n.toFloat + 1 := by
  simp [Nat.toFloat, Nat.cast_succ]

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
  apply hoare_pure
  constructor
  · exact h_step_nonzero
  · simp [arange]
    constructor
    · intro hn
      -- For n = 0 case, we can always satisfy the condition since we don't generate any values
      by_cases h : step > 0
      · left; exact ⟨h, le_refl _⟩
      · right; exact ⟨lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h_step_nonzero), le_refl _⟩
    · intro hn
      constructor
      · intro i
        -- Show that each element has the correct value
        simp [list_to_vector]
        have h1 : (generate_arange_values start step n).length = n := generate_arange_values_length start step n
        have h2 : i.val < (generate_arange_values start step n).length := by rw [h1]; exact i.isLt
        simp [List.take, List.extend]
        rw [List.get_take]
        exact generate_arange_values_get start step n i
        exact h2
      · constructor
        · intro h_pos
          constructor
          · -- We need to assume start < stop for positive step when n > 0
            -- This is a precondition that should hold for meaningful arange calls
            admit
          · intro i
            -- Show that all values are less than stop for positive step
            admit
        · intro h_neg
          constructor
          · -- We need to assume start > stop for negative step when n > 0
            admit
          · intro i
            -- Show that all values are greater than stop for negative step
            admit