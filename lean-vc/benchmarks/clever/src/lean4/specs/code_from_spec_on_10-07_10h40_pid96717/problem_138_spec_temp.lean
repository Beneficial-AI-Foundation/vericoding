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
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Even_Int (n : Int) : Prop := ∃ k : Int, n = 2 * k

-- LLM HELPER
lemma even_zero : Even 0 := ⟨0, rfl⟩

-- LLM HELPER
lemma even_two_mul (k : Nat) : Even (2 * k) := ⟨k, rfl⟩

-- LLM HELPER
lemma even_add (a b : Nat) : Even a → Even b → Even (a + b) := by
  intro ⟨k1, h1⟩ ⟨k2, h2⟩
  use k1 + k2
  rw [h1, h2]
  ring

-- LLM HELPER
lemma int_coe_nat_even (n : Nat) : Even n → Even_Int (Int.ofNat n) := by
  intro ⟨k, hk⟩
  use Int.ofNat k
  rw [hk]
  simp

-- LLM HELPER
lemma int_even_coe_nat (n : Nat) : Even_Int (Int.ofNat n) → Even n := by
  intro ⟨k, hk⟩
  cases' k with k' k'
  · use k'
    simp at hk
    exact hk
  · simp at hk
    have : Int.ofNat n = Int.negSucc k' := hk
    simp at this

-- LLM HELPER
lemma even_sum_characterization (n : Int) :
  (∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n)) ↔ 
  (n ≥ 0 ∧ Even_Int n) := by
  constructor
  · intro ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩
    constructor
    · rw [← h_sum]
      simp only [Int.ofNat_add]
      exact Int.ofNat_nonneg _
    · rw [← h_sum]
      simp only [Int.ofNat_add]
      apply int_coe_nat_even
      apply even_add
      · apply even_add
        · apply even_add <;> assumption
        · exact hc
      · exact hd
  · intro ⟨h_nonneg, h_even⟩
    cases' Int.natAbs_eq h_nonneg with h
    rw [← h] at h_even
    have : Even (Int.natAbs n) := int_even_coe_nat (Int.natAbs n) h_even
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
      simp

def implementation (n: Int) : Bool := n ≥ 0 ∧ Even_Int n

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec
  simp only [implementation]
  use (n ≥ 0 ∧ Even_Int n)
  constructor
  · rfl
  · intro result
    rw [even_sum_characterization]
    rfl