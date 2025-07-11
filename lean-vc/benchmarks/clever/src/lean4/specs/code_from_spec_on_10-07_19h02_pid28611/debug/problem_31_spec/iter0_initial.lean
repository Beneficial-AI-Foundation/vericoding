import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def has_divisor_in_range (n : Nat) (start : Nat) : Bool :=
  if start >= n then false
  else if start < 2 then has_divisor_in_range n 2
  else if n % start = 0 then true
  else has_divisor_in_range n (start + 1)

def implementation (n: Nat): Bool := 
  if n < 2 then false
  else ¬ (has_divisor_in_range n 2)

-- LLM HELPER
theorem has_divisor_in_range_spec (n start : Nat) :
  has_divisor_in_range n start = true ↔ 
  ∃ k, start ≤ k ∧ k < n ∧ 2 ≤ k ∧ n % k = 0 := by
  sorry

-- LLM HELPER
theorem has_divisor_in_range_false (n start : Nat) :
  has_divisor_in_range n start = false ↔ 
  ¬ ∃ k, start ≤ k ∧ k < n ∧ 2 ≤ k ∧ n % k = 0 := by
  sorry

-- LLM HELPER
theorem aux_lemma (n : Nat) :
  (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) ↔ 
  (∃ k, 2 ≤ k ∧ k < n ∧ 2 ≤ k ∧ n % k = 0) := by
  constructor
  · intro h
    obtain ⟨k, hk1, hk2, hk3⟩ := h
    exact ⟨k, hk1, hk2, hk1, hk3⟩
  · intro h
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h
    exact ⟨k, hk1, hk2, hk4⟩

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  unfold implementation
  simp only [exists_prop]
  split_ifs with h
  · -- case n < 2
    simp
    constructor
    · rfl
    · simp
      intro k hk1 hk2
      omega
  · -- case n ≥ 2
    simp
    constructor
    · rfl
    · simp [Bool.not_eq_true]
      rw [has_divisor_in_range_false]
      simp
      rw [← aux_lemma]
      simp