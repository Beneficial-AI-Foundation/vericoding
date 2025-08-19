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
      let diff := Float.abs (desired.get ⟨i, by 
        simp only [Membership.mem, List.mem_range]
        exact Nat.lt_of_mem_range (List.mem_range.mp ‹i ∈ List.range n›)⟩ - actual.get ⟨i, by 
        simp only [Membership.mem, List.mem_range]
        exact Nat.lt_of_mem_range (List.mem_range.mp ‹i ∈ List.range n›)⟩)
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
  constructor
  · intro h
    constructor
    · intro i
      by_cases h_dec : decimal ≥ 1
      · have h_check : check_tolerance (Float.abs (desired.get i - actual.get i)) decimal = true := by
          simp_all [h, check_tolerance, h_dec]
        rw [check_tolerance] at h_check
        simp [h_dec] at h_check
        exact h_check
      · have h_check : check_tolerance (Float.abs (desired.get i - actual.get i)) decimal = true := by
          simp_all [h, check_tolerance, h_dec]
        rw [check_tolerance] at h_check
        simp [h_dec] at h_check
        exact h_check
    · constructor
      · intro i
        rw [Float.abs_sub_comm]
      · constructor
        · intro h_eq
          rw [h_eq]
          simp [Float.abs_sub_self]
        · constructor
          · intro h_dec0 i
            simp [h_dec0]
            have h_check : check_tolerance (Float.abs (desired.get i - actual.get i)) decimal = true := by
              simp_all [h, check_tolerance]
            rw [check_tolerance] at h_check
            have h_not_ge : ¬(decimal ≥ 1) := by
              rw [h_dec0]
              norm_num
            simp [h_not_ge] at h_check
            exact h_check
          · intro h_dec1 i
            have h_check : check_tolerance (Float.abs (desired.get i - actual.get i)) decimal = true := by
              simp_all [h, check_tolerance]
            rw [check_tolerance] at h_check
            simp [h_dec1] at h_check
            exact h_check
  · intro h
    cases' h with h1 h_rest
    intro i
    have h_tol := h1 i
    simp [check_tolerance]
    by_cases h_dec : decimal ≥ 1
    · simp [h_dec]
      exact h_tol
    · simp [h_dec]
      exact h_tol