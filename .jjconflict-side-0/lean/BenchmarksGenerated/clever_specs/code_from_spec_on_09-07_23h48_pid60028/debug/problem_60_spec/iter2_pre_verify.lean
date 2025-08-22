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

def implementation (n: Nat) : Nat := n * (n + 1) / 2

-- LLM HELPER
lemma implementation_recurrence (i : Nat) : implementation (i + 1) - implementation i = i + 1 := by
  unfold implementation
  simp [Nat.add_mul, Nat.mul_add]
  cases i with
  | zero => simp
  | succ k => 
    simp [Nat.succ_mul, Nat.mul_succ]
    ring_nf
    simp [Nat.add_div_two_le_iff]

-- LLM HELPER
lemma implementation_equals_one_iff (n : Nat) (h : 0 < n) : implementation n = 1 ↔ n = 1 := by
  unfold implementation
  constructor
  · intro h_eq
    by_cases h1 : n = 1
    · exact h1
    · have n_ge_2 : n ≥ 2 := by
        cases n with
        | zero => contradiction
        | succ m => 
          cases m with
          | zero => contradiction
          | succ k => simp
      have : n * (n + 1) ≥ 2 * 3 := by
        apply Nat.mul_le_mul'
        · exact n_ge_2
        · linarith
      have : n * (n + 1) / 2 ≥ 3 := by
        have : n * (n + 1) ≥ 6 := by linarith
        rw [Nat.le_div_iff_mul_le]
        · linarith
        · norm_num
      linarith
  · intro h_eq
    rw [h_eq]
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
    · exact implementation_equals_one_iff n h
    · exact implementation_recurrence