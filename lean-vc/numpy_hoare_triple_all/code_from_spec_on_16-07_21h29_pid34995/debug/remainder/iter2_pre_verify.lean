import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.remainder: Returns the element-wise remainder of division.

    Computes the remainder complementary to the floor_divide function.
    This is equivalent to x1 % x2 in terms of array broadcasting.
    
    The result has the same sign as the divisor x2.
    For floating point inputs, the result is mathematically defined as:
    x1 - floor(x1/x2) * x2
    
    From NumPy documentation:
    - Parameters: x1, x2 (array_like) - The dividend and divisor arrays
    - Returns: remainder (ndarray) - The element-wise remainder of x1 divided by x2
    - This is a universal function (ufunc) implemented in C
    - Uses optimized C loops for different data types
-/
def remainder {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => x1.get i - (x1.get i / x2.get i).floor * x2.get i)

-- LLM HELPER
lemma float_remainder_properties (a b : Float) (hb : b ≠ 0) :
    let r := a - (a / b).floor * b
    a = (a / b).floor * b + r ∧
    (b > 0 → r ≥ 0 ∧ r < b) ∧
    (b < 0 → r ≤ 0 ∧ r > b) ∧
    Float.abs r < Float.abs b := by
  simp only [show a - (a / b).floor * b = a - (a / b).floor * b from rfl]
  constructor
  · ring
  constructor
  · intro hb_pos
    constructor
    · -- r ≥ 0 when b > 0
      have h1 : (a / b).floor ≤ a / b := Float.floor_le _
      have h2 : a / b < (a / b).floor + 1 := Float.lt_floor_add_one _
      rw [← Float.div_le_iff hb_pos] at h1
      rw [← Float.div_lt_iff hb_pos] at h2
      linarith
    · -- r < b when b > 0
      have h1 : (a / b).floor ≤ a / b := Float.floor_le _
      have h2 : a / b < (a / b).floor + 1 := Float.lt_floor_add_one _
      rw [← Float.div_lt_iff hb_pos] at h2
      have : a < ((a / b).floor + 1) * b := h2
      linarith
  constructor
  · intro hb_neg
    constructor
    · -- r ≤ 0 when b < 0
      have h1 : (a / b).floor ≤ a / b := Float.floor_le _
      have h2 : a / b < (a / b).floor + 1 := Float.lt_floor_add_one _
      have hb_neg' : b < 0 := hb_neg
      rw [← Float.div_le_iff_of_neg hb_neg'] at h1
      rw [← Float.div_lt_iff_of_neg hb_neg'] at h2
      linarith
    · -- r > b when b < 0
      have h1 : (a / b).floor ≤ a / b := Float.floor_le _
      have h2 : a / b < (a / b).floor + 1 := Float.lt_floor_add_one _
      have hb_neg' : b < 0 := hb_neg
      rw [← Float.div_lt_iff_of_neg hb_neg'] at h2
      have : a > ((a / b).floor + 1) * b := h2
      linarith
  · -- |r| < |b|
    have h1 : (a / b).floor ≤ a / b := Float.floor_le _
    have h2 : a / b < (a / b).floor + 1 := Float.lt_floor_add_one _
    cases' Float.lt_or_gt_of_ne hb with hb_pos hb_neg
    · -- b > 0 case
      have r_nonneg : a - (a / b).floor * b ≥ 0 := by
        rw [← Float.div_le_iff hb_pos] at h1
        linarith
      have r_lt_b : a - (a / b).floor * b < b := by
        rw [← Float.div_lt_iff hb_pos] at h2
        have : a < ((a / b).floor + 1) * b := h2
        linarith
      rw [Float.abs_of_nonneg r_nonneg, Float.abs_of_pos hb_pos]
      exact r_lt_b
    · -- b < 0 case
      have r_nonpos : a - (a / b).floor * b ≤ 0 := by
        rw [← Float.div_le_iff_of_neg hb_neg] at h1
        linarith
      have r_gt_b : a - (a / b).floor * b > b := by
        rw [← Float.div_lt_iff_of_neg hb_neg] at h2
        have : a > ((a / b).floor + 1) * b := h2
        linarith
      rw [Float.abs_of_nonpos r_nonpos, Float.abs_of_neg hb_neg]
      linarith

/-- Specification: numpy.remainder returns a vector where each element is the remainder
    of the corresponding elements from x1 and x2.

    Mathematical Properties:
    1. Element-wise correctness: result[i] = x1[i] % x2[i]
    2. Complementary to floor division: x1[i] = floor(x1[i]/x2[i]) * x2[i] + result[i]
    3. Sign follows divisor: result[i] has the same sign as x2[i] (when x2[i] ≠ 0)
    4. Magnitude bound: |result[i]| < |x2[i]| (when x2[i] ≠ 0)
    5. Mathematical definition: result[i] = x1[i] - floor(x1[i]/x2[i]) * x2[i]
    6. Preserves vector length: result.size = x1.size = x2.size
    7. Handles IEEE 754 floating-point arithmetic

    Precondition: All elements in x2 must be non-zero
    Postcondition: For all indices i, result[i] satisfies the remainder properties
-/
theorem remainder_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    remainder x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, 
      let r := result.get i
      let a := x1.get i  
      let b := x2.get i
      -- Mathematical definition: a = floor(a/b) * b + r
      a = (a / b).floor * b + r ∧
      -- Result has same sign as divisor (when divisor is non-zero)
      (b > 0 → r ≥ 0 ∧ r < b) ∧
      (b < 0 → r ≤ 0 ∧ r > b) ∧
      -- Magnitude bound
      Float.abs r < Float.abs b⌝⦄ := by
  intro h
  simp only [remainder]
  intro i
  simp only [Vector.get_ofFn]
  exact float_remainder_properties (x1.get i) (x2.get i) (h i)