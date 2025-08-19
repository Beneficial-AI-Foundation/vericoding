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
      simp only [Int.coe_nat_add]
      apply Int.coe_nat_nonneg
    · rw [← h_sum]
      simp only [Int.coe_nat_add]
      apply Even.add_even
      · apply Even.add_even
        · apply Even.add_even <;> exact Int.coe_nat_even_iff.mpr
          exact ha
          exact hb
        · exact Int.coe_nat_even_iff.mpr hc
      · exact Int.coe_nat_even_iff.mpr hd
  · intro ⟨h_nonneg, h_even⟩
    cases' Int.natAbs_eq h_nonneg with h
    rw [← h] at h_even
    have : Even (Int.natAbs n) := Int.coe_nat_even_iff.mp h_even
    cases' this with k hk
    use 2*k, 0, 0, 0
    constructor
    · exact even_two_mul k
    constructor
    · exact even_zero
    constructor
    · exact even_zero
    constructor
    · exact even_zero
    · rw [← h, hk]
      simp only [Int.coe_nat_add, Int.coe_nat_zero, add_zero, Int.coe_nat_mul]

def implementation (n: Int) : Bool := n ≥ 0 ∧ Even n

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec
  simp only [implementation]
  use (n ≥ 0 ∧ Even n)
  constructor
  · rfl
  · intro result
    rw [even_sum_characterization]
    rfl