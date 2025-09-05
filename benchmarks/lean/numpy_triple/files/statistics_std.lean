/-  numpy.std: Compute the standard deviation along the specified axis.

    Returns the standard deviation, a measure of the spread of a distribution,
    of the array elements. The standard deviation is computed for the flattened
    array by default, otherwise over the specified axis.

    The standard deviation is the square root of the average of the squared
    deviations from the mean: std = sqrt(mean((x - x.mean())**2)).

    With ddof parameter, the divisor used in calculations is N - ddof,
    where N represents the number of elements. The "Delta Degrees of Freedom"
    parameter adjusts the divisor in the standard deviation calculation.
-/

/-  Specification: numpy.std returns the standard deviation of all elements.

    The standard deviation is computed as the square root of the variance:
    std = sqrt(sum((x_i - mean)²) / (N - ddof))

    Key properties:
    1. ddof must be less than the number of elements to avoid division by zero
    2. The result is always non-negative (square root of non-negative variance)
    3. When ddof = 0, uses population standard deviation (divide by N)
    4. When ddof = 1, uses sample standard deviation (divide by N-1)
    5. Mathematical correctness: the formula exactly matches NumPy's implementation
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_std {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat := 0) : Id Float :=
  sorry

theorem numpy_std_spec {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h_ddof : ddof < n + 1) :
    ⦃⌜ddof < n + 1⌝⦄
    numpy_std a ddof
    ⦃⇓result => ⌜
      let N := n + 1
      let mean := (List.sum (a.toList)) / Float.ofNat N
      let squared_deviations := a.toList.map (fun x => (x - mean) * (x - mean))
      let variance := (List.sum squared_deviations) / Float.ofNat (N - ddof)
      result = Float.sqrt variance ∧
      result ≥ 0 ∧
      (∀ i : Fin (n + 1), a.get i = mean → result = 0) ∧
      (N - ddof > 0)⌝⦄ := by
  sorry
