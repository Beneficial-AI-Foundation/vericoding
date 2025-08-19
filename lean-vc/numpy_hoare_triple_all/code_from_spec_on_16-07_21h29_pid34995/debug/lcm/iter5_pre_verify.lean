import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.lcm: Returns the lowest common multiple of |x1| and |x2| element-wise.

    Computes the lowest common multiple (LCM) of the absolute values of 
    the elements in x1 and x2. The LCM is the smallest non-negative integer 
    that is a multiple of both |x1| and |x2|.

    Mathematical Properties:
    - lcm(a, b) = lcm(b, a) (commutativity)
    - lcm(a, b) * gcd(a, b) = |a * b| (fundamental relationship)
    - lcm(0, b) = lcm(a, 0) = 0 (zero property)
    - lcm(a, b) ≥ 0 (non-negativity)
    - |a| divides lcm(a, b) and |b| divides lcm(a, b) (divisibility)
    - lcm(a, b) is minimal among all positive integers divisible by both |a| and |b|

    Examples:
    - lcm(4, 6) = 12
    - lcm(-4, 6) = 12 (uses absolute values)
    - lcm(0, 5) = 0 (LCM with zero is always zero)
    - lcm(8, 12) = 24
    - lcm(7, 11) = 77 (coprime numbers)
-/
def lcm {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  pure (Vector.ofFn (fun i => Int.lcm (x1.get i) (x2.get i)))

-- LLM HELPER
theorem int_lcm_nonneg (a b : Int) : Int.lcm a b ≥ 0 := by
  simp [Int.lcm]
  exact Int.coe_nat_nonneg _

-- LLM HELPER
theorem int_lcm_zero_left (b : Int) : Int.lcm 0 b = 0 := by
  simp [Int.lcm]

-- LLM HELPER
theorem int_lcm_zero_right (a : Int) : Int.lcm a 0 = 0 := by
  simp [Int.lcm]

-- LLM HELPER
theorem int_lcm_comm (a b : Int) : Int.lcm a b = Int.lcm b a := by
  simp [Int.lcm]
  rw [Nat.lcm_comm]

-- LLM HELPER
theorem int_lcm_gcd_mul (a b : Int) : a ≠ 0 → b ≠ 0 → 
  Int.natAbs (Int.lcm a b) * Int.gcd a b = Int.natAbs a * Int.natAbs b := by
  intro ha hb
  simp [Int.lcm]
  rw [Int.natAbs_of_nonneg (Int.coe_nat_nonneg _)]
  conv_rhs => rw [← Nat.lcm_mul_gcd (Int.natAbs a) (Int.natAbs b)]
  simp [Int.gcd]

-- LLM HELPER
theorem int_lcm_dvd (a b : Int) : a ≠ 0 → b ≠ 0 → 
  (Int.natAbs a : Int) ∣ Int.lcm a b ∧ (Int.natAbs b : Int) ∣ Int.lcm a b := by
  intro ha hb
  simp [Int.lcm]
  constructor
  · apply Int.coe_nat_dvd.mpr
    exact Nat.dvd_lcm_left (Int.natAbs a) (Int.natAbs b)
  · apply Int.coe_nat_dvd.mpr
    exact Nat.dvd_lcm_right (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
theorem int_lcm_minimal (a b : Int) : ∀ (m : Int), m ≥ 0 → 
  (Int.natAbs a : Int) ∣ m → (Int.natAbs b : Int) ∣ m → 
  a ≠ 0 → b ≠ 0 → Int.lcm a b ≤ m := by
  intro m hm hdva hdvb ha hb
  simp [Int.lcm]
  have hm_nat : ∃ k : Nat, m = k := by
    use m.natAbs
    exact Int.eq_natAbs_of_nonneg hm
  obtain ⟨k, hk⟩ := hm_nat
  rw [hk]
  simp
  rw [hk] at hdva hdvb
  have hdva_nat : Int.natAbs a ∣ k := Int.coe_nat_dvd.mp hdva
  have hdvb_nat : Int.natAbs b ∣ k := Int.coe_nat_dvd.mp hdvb
  exact Nat.lcm_le_of_dvd (Int.natAbs_pos ha) hdva_nat hdvb_nat

-- LLM HELPER
theorem int_lcm_pos (a b : Int) : a ≠ 0 → b ≠ 0 → Int.lcm a b > 0 := by
  intro ha hb
  simp [Int.lcm]
  exact Int.coe_nat_pos.mpr (Nat.lcm_pos (Int.natAbs_pos ha) (Int.natAbs_pos hb))

/-- Specification: lcm returns a vector where each element is the lowest 
    common multiple of the absolute values of the corresponding elements 
    from x1 and x2.

    Precondition: True (no special preconditions)
    
    Postcondition: 
    1. Each element of the result is the LCM of |x1[i]| and |x2[i]|
    2. The result satisfies the mathematical properties of LCM:
       - Non-negativity: lcm(a, b) ≥ 0 (always true by definition)
       - Zero property: lcm(0, b) = lcm(a, 0) = 0
       - Commutativity: lcm(a, b) = lcm(b, a) (implicit in Int.lcm)
       - Relationship with GCD: lcm(a, b) * gcd(a, b) = |a * b|
       - Divisibility: |a| divides lcm(a, b) and |b| divides lcm(a, b)
       - Minimality: lcm(a, b) is the smallest non-negative integer divisible by both |a| and |b| (when both are non-zero)
    3. Special cases:
       - When either input is zero, the result is zero
       - When inputs are coprime (gcd = 1), lcm = |a * b|
-/
theorem lcm_spec {n : Nat} (x1 x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    lcm x1 x2
    ⦃⇓result => ⌜-- Basic correctness: each element is the LCM of corresponding elements
                 (∀ i : Fin n, result.get i = (Int.lcm (x1.get i) (x2.get i) : Int)) ∧
                 -- Non-negativity: LCM is always non-negative
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 -- Zero property: LCM with zero is zero
                 (∀ i : Fin n, (x1.get i = 0 ∨ x2.get i = 0) → result.get i = 0) ∧
                 -- Commutativity: LCM is commutative
                 (∀ i : Fin n, result.get i = (Int.lcm (x2.get i) (x1.get i) : Int)) ∧
                 -- Fundamental LCM-GCD relationship: lcm(a,b) * gcd(a,b) = |a * b|
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → 
                    Int.natAbs (result.get i) * Int.gcd (x1.get i) (x2.get i) = Int.natAbs (x1.get i) * Int.natAbs (x2.get i)) ∧
                 -- Divisibility: both absolute values divide the LCM
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → 
                    (Int.natAbs (x1.get i) : Int) ∣ result.get i ∧ (Int.natAbs (x2.get i) : Int) ∣ result.get i) ∧
                 -- Minimality: LCM is the smallest non-negative integer divisible by both absolute values
                 (∀ i : Fin n, ∀ (m : Int), m ≥ 0 → 
                    (Int.natAbs (x1.get i) : Int) ∣ m → (Int.natAbs (x2.get i) : Int) ∣ m → 
                    x1.get i ≠ 0 → x2.get i ≠ 0 → result.get i ≤ m) ∧
                 -- Special case: when both are non-zero, LCM is positive
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → result.get i > 0)⌝⦄ := by
  simp [lcm]
  constructor
  · intro i
    simp [Vector.get_ofFn]
  constructor
  · intro i
    simp [Vector.get_ofFn]
    exact int_lcm_nonneg _ _
  constructor
  · intro i h
    simp [Vector.get_ofFn]
    cases h with
    | inl h => rw [h, int_lcm_zero_left]
    | inr h => rw [h, int_lcm_zero_right]
  constructor
  · intro i
    simp [Vector.get_ofFn]
    exact int_lcm_comm _ _
  constructor
  · intro i h1 h2
    simp [Vector.get_ofFn]
    exact int_lcm_gcd_mul _ _ h1 h2
  constructor
  · intro i h1 h2
    simp [Vector.get_ofFn]
    exact int_lcm_dvd _ _ h1 h2
  constructor
  · intro i m hm hdv1 hdv2 h1 h2
    simp [Vector.get_ofFn]
    exact int_lcm_minimal _ _ m hm hdv1 hdv2 h1 h2
  · intro i h1 h2
    simp [Vector.get_ofFn]
    exact int_lcm_pos _ _ h1 h2