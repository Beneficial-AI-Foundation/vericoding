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
lemma even_sum_characterization (n : Int) : 
  (∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n)) ↔ 
  (n ≥ 0 ∧ Even n) := by
  constructor
  · intro ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩
    constructor
    · rw [← h_sum]
      simp [Int.natCast_nonneg]
    · rw [← h_sum]
      simp [Int.natCast_add]
      apply Even.add_even
      · apply Even.add_even
        · apply Even.add_even <;> exact Int.even_coe_nat.mpr ‹_›
        · exact Int.even_coe_nat.mpr hc
      · exact Int.even_coe_nat.mpr hd
  · intro ⟨h_nonneg, h_even⟩
    cases' Int.natAbs_eq with h
    rw [← h] at h_even
    simp only [Int.even_coe_nat] at h_even
    obtain ⟨k, hk⟩ := h_even
    cases' k with k
    · use 0, 0, 0, 0
      simp [hk, h]
    · cases' k with k
      · use 0, 0, 0, 2
        simp [hk, h]
      · cases' k with k
        · use 0, 0, 2, 2
          simp [hk, h]
        · use 0, 2, 2, 2 * k
          simp [hk, h]
          ring

def implementation (n: Int) : Bool := decide (n ≥ 0 ∧ Even n)

theorem correctness
(n: Int)
: problem_spec implementation n := by
  use (decide (n ≥ 0 ∧ Even n))
  constructor
  · rfl
  · simp only [Bool.decide_eq_true_iff]
    exact even_sum_characterization n