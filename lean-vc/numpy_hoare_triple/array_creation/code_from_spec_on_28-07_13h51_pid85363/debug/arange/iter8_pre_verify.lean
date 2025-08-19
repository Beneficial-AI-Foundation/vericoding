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
def makeArangeVector {n : Nat} (start step : Float) : Vector Float n :=
  Vector.ofFn (fun i => start + (i.val.toFloat) * step)

/-- Return evenly spaced values within a given interval [start, stop) with given step -/
def arange {n : Nat} (start : Float) (_ : Float) (step : Float) : Id (Vector Float n) :=
  pure (makeArangeVector start step)

-- LLM HELPER
theorem makeArangeVector_get {n : Nat} (start step : Float) (i : Fin n) :
    (makeArangeVector start step).get i = start + (i.val.toFloat) * step := by
  simp [makeArangeVector, Vector.get_ofFn]

-- LLM HELPER  
theorem nat_toFloat_nonneg (n : Nat) : (n.toFloat) ≥ 0 := by
  simp [Nat.toFloat, Float.ofNat]
  exact Float.ofNat_nonneg n

-- LLM HELPER
theorem fin_val_toFloat_nonneg {n : Nat} (i : Fin n) : (i.val.toFloat) ≥ 0 := by
  exact nat_toFloat_nonneg i.val

-- LLM HELPER
theorem step_pos_mul_nonneg (step : Float) (x : Float) (h_step : step > 0) (h_x : x ≥ 0) : 
    step * x ≥ 0 := by
  exact Float.mul_nonneg (le_of_lt h_step) h_x

-- LLM HELPER
theorem step_neg_mul_nonpos (step : Float) (x : Float) (h_step : step < 0) (h_x : x ≥ 0) : 
    step * x ≤ 0 := by
  exact Float.mul_nonpos_of_neg_of_nonneg h_step h_x

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
  simp [arange]
  constructor
  · intro h_n_zero
    by_cases h : step > 0
    · left
      constructor
      · exact h
      · trivial
    · right
      constructor
      · cases' lt_or_gt_of_ne h_step_nonzero with h_neg h_pos
        · exact h_neg
        · contradiction
      · trivial
  · intro h_n_pos
    constructor
    · intro i
      exact makeArangeVector_get start step i
    · constructor
      · intro h_step_pos
        constructor
        · trivial
        · intro i
          trivial
      · intro h_step_neg
        constructor
        · trivial
        · intro i
          trivial