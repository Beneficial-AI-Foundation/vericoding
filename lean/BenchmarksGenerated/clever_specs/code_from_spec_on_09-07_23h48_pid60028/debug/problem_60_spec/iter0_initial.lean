def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def implementation (n: Nat) : Nat := n * (n + 1) / 2

-- LLM HELPER
lemma implementation_recurrence (i : Nat) : implementation (i + 1) - implementation i = i + 1 := by
  unfold implementation
  simp [Nat.add_mul, Nat.mul_add]
  ring_nf
  rw [Nat.add_div_two_le_iff]
  ring

-- LLM HELPER
lemma implementation_equals_one_iff (n : Nat) : implementation n = 1 ↔ n = 1 := by
  unfold implementation
  constructor
  · intro h
    by_cases h1 : n = 0
    · simp [h1] at h
    · by_cases h2 : n = 1
      · exact h2
      · have : n ≥ 2 := by
          cases n with
          | zero => contradiction
          | succ m => 
            cases m with
            | zero => contradiction
            | succ k => simp [Nat.succ_le_iff]
        have : n * (n + 1) ≥ 2 * 3 := by
          apply Nat.mul_le_mul'
          · exact this
          · linarith
        have : n * (n + 1) / 2 ≥ 3 := by
          rw [Nat.div_le_iff_le_mul_left]
          · linarith
          · norm_num
        linarith
  · intro h
    rw [h]
    simp

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro h
    constructor
    · exact implementation_equals_one_iff n
    · exact implementation_recurrence