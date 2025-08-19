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
lemma four_evens_sum_even (a b c d : Nat) (ha : Even a) (hb : Even b) (hc : Even c) (hd : Even d) :
  Even (a + b + c + d) := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  obtain ⟨kc, hkc⟩ := hc
  obtain ⟨kd, hkd⟩ := hd
  use ka + kb + kc + kd
  rw [hka, hkb, hkc, hkd]
  ring

-- LLM HELPER
lemma int_even_iff_nat_even (n : Int) (hn : n ≥ 0) : Even n ↔ Even n.natAbs := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    use k.natAbs
    rw [← Int.natAbs_mul, hk, Int.natAbs_of_nonneg hn]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    rw [← Int.natAbs_of_nonneg hn, hk]
    simp

-- LLM HELPER
lemma sum_four_evens_exists_iff_even_nonneg (n : Int) (hn : n ≥ 0) :
  (∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n)) ↔ 
  Even n ∧ n ≥ 0 := by
  constructor
  · intro ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩
    constructor
    · rw [← h_sum]
      exact Int.coe_nat_even_iff.mpr (four_evens_sum_even a b c d ha hb hc hd)
    · exact hn
  · intro ⟨h_even, h_nonneg⟩
    have h_nat_even : Even n.natAbs := by
      rwa [← int_even_iff_nat_even n h_nonneg]
    obtain ⟨k, hk⟩ := h_nat_even
    use 2*k, 0, 0, 0
    constructor
    · exact even_two_mul k
    constructor
    · exact even_zero
    constructor
    · exact even_zero
    constructor
    · exact even_zero
    · rw [add_zero, add_zero, add_zero]
      rw [Int.natAbs_of_nonneg h_nonneg] at hk
      exact hk.symm

def implementation (n: Int) : Bool := n ≥ 0 ∧ Even n

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec
  simp [implementation]
  by_cases h : n ≥ 0 ∧ Even n
  · use true
    constructor
    · simp [h]
    · simp
      cases' h with h_nonneg h_even
      exact sum_four_evens_exists_iff_even_nonneg n h_nonneg
  · use false
    constructor
    · simp [h]
    · simp
      push_neg at h
      intro a b c d ha hb hc hd h_sum
      cases' h with h_neg h_odd
      · have h_nonneg : n ≥ 0 := by
          rw [← h_sum]
          exact Nat.cast_nonneg (a + b + c + d)
        exact h_neg h_nonneg
      · have h_even : Even n := by
          rw [← h_sum]
          exact Int.coe_nat_even_iff.mpr (four_evens_sum_even a b c d ha hb hc hd)
        exact h_odd h_even