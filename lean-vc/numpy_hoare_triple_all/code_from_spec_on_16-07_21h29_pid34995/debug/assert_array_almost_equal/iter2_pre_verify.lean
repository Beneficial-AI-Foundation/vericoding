import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def check_tolerance (diff : Float) (decimal : Nat) : Bool :=
  if decimal ≥ 1 then
    diff < 1.5 * (10 : Float) ^ (-(decimal : Nat).toFloat)
  else
    diff < (10 : Float) ^ (-(decimal : Nat).toFloat)

/-- Check if two vectors are almost equal up to desired precision.
    Returns true if the assertion passes, false if it would raise an AssertionError. -/
def assert_array_almost_equal {n : Nat} (actual desired : Vector Float n) (decimal : Nat := 6) : Id Bool :=
  do
    let mut result := true
    for i in [0:n] do
      let diff := Float.abs (desired.get ⟨i, by omega⟩ - actual.get ⟨i, by omega⟩)
      if ¬(check_tolerance diff decimal) then
        result := false
        break
    return result

/-- Specification: assert_array_almost_equal checks if two arrays are almost equal up to desired precision.
    The function verifies that abs(desired[i] - actual[i]) < tolerance for all elements.
    Mathematical properties:
    1. Symmetry: almost_equal(a, b) = almost_equal(b, a)
    2. Reflexivity: almost_equal(a, a) = True
    3. Tolerance bound: abs(desired[i] - actual[i]) < tolerance for success
    4. Precision scaling: smaller decimal means looser tolerance
    5. Element-wise comparison: all elements must satisfy the tolerance individually -/
theorem assert_array_almost_equal_spec {n : Nat} (actual desired : Vector Float n) (decimal : Nat) :
    ⦃⌜True⌝⦄
    assert_array_almost_equal actual desired decimal
    ⦃⇓result => ⌜result = true ↔ 
                  (let tolerance := if decimal ≥ 1 then 1.5 * (10 : Float) ^ (-(decimal : Nat).toFloat) else (10 : Float) ^ (-(decimal : Nat).toFloat)
                   ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < tolerance) ∧
                  (∀ i : Fin n, Float.abs (actual.get i - desired.get i) = Float.abs (desired.get i - actual.get i)) ∧
                  (actual = desired → result = true) ∧
                  (decimal = 0 → ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < (10 : Float) ^ (-(decimal : Nat).toFloat)) ∧
                  (decimal ≥ 1 → ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < 1.5 * (10 : Float) ^ (-(decimal : Nat).toFloat))⌝⦄ := by
  unfold assert_array_almost_equal
  wp_do
  wp_let
  wp_for_range
  · wp_pure
    simp
  · intro i h_mem
    wp_let
    wp_if
    · wp_assign
      wp_break
      simp
    · wp_continue
      simp