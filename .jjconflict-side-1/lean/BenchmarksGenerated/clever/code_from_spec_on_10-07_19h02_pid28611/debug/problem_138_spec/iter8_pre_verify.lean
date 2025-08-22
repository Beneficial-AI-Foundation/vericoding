import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Int → Bool)
-- inputs
(n: Int) :=
-- spec
let spec (result: Bool) :=
  let sum_exists := ∃ a b c d : Nat,
    Even a ∧
    Even b ∧
    Even c ∧
    Even d ∧
    (a + b + c + d = n);
  result = true ↔ sum_exists
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma sum_four_evens_is_even (a b c d : Nat) : Even a → Even b → Even c → Even d → Even (a + b + c + d) := by
  intros ha hb hc hd
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  obtain ⟨kc, hkc⟩ := hc
  obtain ⟨kd, hkd⟩ := hd
  use ka + kb + kc + kd
  rw [hka, hkb, hkc, hkd]
  ring

-- LLM HELPER
lemma exists_four_even_nats_sum_to_even_nat (m : Nat) : Even m → ∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = m) := by
  intro h
  use 0, 0, 0, m
  constructor
  · exact even_zero
  constructor
  · exact even_zero
  constructor
  · exact even_zero
  constructor
  · exact h
  · simp

-- LLM HELPER
lemma not_exists_four_even_nats_sum_to_odd_nat (m : Nat) : Odd m → ¬∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = m) := by
  intro h_odd h_exists
  obtain ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩ := h_exists
  have h_even_sum : Even (a + b + c + d) := sum_four_evens_is_even a b c d ha hb hc hd
  rw [h_sum] at h_even_sum
  exact Nat.not_even_iff_odd.mp h_odd h_even_sum

def implementation (n: Int) : Bool := 
  if n < 0 then false else Even (Int.natAbs n)

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · unfold implementation
    by_cases h : n < 0
    · simp [h]
      constructor
      · intro h_contra
        exfalso
        obtain ⟨a, b, c, d, _, _, _, _, h_sum⟩ := h_contra
        have h_nonneg : 0 ≤ ↑a + ↑b + ↑c + ↑d := by
          simp only [Int.coe_nat_add]
          exact Nat.cast_nonneg (a + b + c + d)
        rw [← h_sum] at h_nonneg
        exact not_le.mpr h h_nonneg
      · intro h_contra
        cases h_contra
    · simp [h]
      have h_nonneg : 0 ≤ n := le_of_not_gt h
      constructor
      · intro h_even
        have h_even_natabs : Even (Int.natAbs n) := h_even
        obtain ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩ := exists_four_even_nats_sum_to_even_nat (Int.natAbs n) h_even_natabs
        use a, b, c, d
        constructor
        · exact ha
        constructor
        · exact hb
        constructor
        · exact hc
        constructor
        · exact hd
        · rw [Int.natAbs_of_nonneg h_nonneg] at h_sum
          simp only [Int.coe_nat_add]
          exact h_sum
      · intro h_exists
        obtain ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩ := h_exists
        have h_even_sum : Even (a + b + c + d) := sum_four_evens_is_even a b c d ha hb hc hd
        have h_even_cast : Even (↑(a + b + c + d) : Int) := Int.even_coe_nat.mpr h_even_sum
        simp only [Int.coe_nat_add] at h_even_cast
        rw [h_sum] at h_even_cast
        have h_abs_eq : Int.natAbs n = Int.natAbs (↑(a + b + c + d) : Int) := by
          rw [h_sum]
        rw [Int.natAbs_of_nonneg (Nat.cast_nonneg (a + b + c + d))] at h_abs_eq
        rw [Int.natAbs_of_nonneg h_nonneg] at h_abs_eq
        have h_cast_eq : (Int.natAbs n : Int) = ↑(a + b + c + d) := by
          rw [h_abs_eq]
          simp
        rw [← h_cast_eq] at h_even_cast
        exact Int.even_coe_nat.mp h_even_cast