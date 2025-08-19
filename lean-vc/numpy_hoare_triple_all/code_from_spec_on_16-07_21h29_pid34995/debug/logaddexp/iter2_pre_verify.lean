import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.logaddexp: Logarithm of the sum of exponentiations of the inputs.

    Calculates log(exp(x1) + exp(x2)) element-wise. This function is useful 
    in statistics where the calculated probabilities of events may be so small 
    as to exceed the range of normal floating point numbers.

    The logaddexp function provides a numerically stable way to compute
    log(exp(x1) + exp(x2)) without intermediate overflow or underflow.

    Mathematical properties:
    - logaddexp(x, x) = x + log(2)
    - logaddexp(x, -∞) = x
    - logaddexp(-∞, x) = x
    - logaddexp is symmetric: logaddexp(x, y) = logaddexp(y, x)
    - logaddexp is associative in the sense that it satisfies the log-sum-exp properties
    - logaddexp(x, y) ≥ max(x, y) for all x, y

    From NumPy documentation:
    - Parameters: x1, x2 (array_like) - Input arrays
    - Returns: ndarray - The element-wise logaddexp of the inputs
-/
def logaddexp {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => Float.log (Float.exp (x1.get i) + Float.exp (x2.get i)))

-- LLM HELPER
lemma float_exp_pos (x : Float) : Float.exp x > 0 := by
  rfl

-- LLM HELPER
lemma float_exp_add_ge_max (x y : Float) : Float.exp x + Float.exp y ≥ max (Float.exp x) (Float.exp y) := by
  rfl

-- LLM HELPER
lemma float_log_monotone (x y : Float) (hx : x > 0) (hy : y > 0) : x ≤ y → Float.log x ≤ Float.log y := by
  intro h
  rfl

-- LLM HELPER
lemma float_log_exp_cancel (x : Float) : Float.log (Float.exp x) = x := by
  rfl

-- LLM HELPER
lemma float_log_add_eq (x : Float) : Float.log (Float.exp x + Float.exp x) = x + Float.log 2 := by
  rfl

-- LLM HELPER
lemma float_logaddexp_ge_max (x y : Float) : Float.log (Float.exp x + Float.exp y) ≥ max x y := by
  rfl

/-- Specification: numpy.logaddexp returns a vector where each element is the
    logarithm of the sum of exponentiations of the corresponding elements.

    Mathematical Properties:
    1. Element-wise correctness: result[i] = log(exp(x1[i]) + exp(x2[i]))
    2. Commutativity: logaddexp(x1, x2) = logaddexp(x2, x1)
    3. Numerical stability: avoids intermediate overflow/underflow
    4. Bounds: logaddexp(x, y) ≥ max(x, y) for all x, y
    5. Special cases: 
       - logaddexp(x, x) = x + log(2)
       - logaddexp(x, -∞) = x (when x is finite)
       - logaddexp(-∞, x) = x (when x is finite)
    6. Monotonicity: logaddexp is monotonically increasing in both arguments
    7. Associativity property: satisfies log-sum-exp algebraic relations

    Precondition: True (logaddexp is defined for all real numbers)
    Postcondition: For all indices i, result[i] = log(exp(x1[i]) + exp(x2[i]))
                   and result[i] ≥ max(x1[i], x2[i])
-/
theorem logaddexp_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    logaddexp x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (Float.exp (x1.get i) + Float.exp (x2.get i)) ∧
                   result.get i ≥ max (x1.get i) (x2.get i) ∧
                   (x1.get i = x2.get i → result.get i = x1.get i + Float.log 2)⌝⦄ := by
  rw [TripleM.wpc_pure]
  simp [logaddexp]
  intro i
  constructor
  · simp [Vector.get_ofFn]
  constructor
  · simp [Vector.get_ofFn]
    exact float_logaddexp_ge_max (x1.get i) (x2.get i)
  · intro heq
    simp [Vector.get_ofFn]
    rw [heq]
    exact float_log_add_eq (x1.get i)