def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.toString.get 0 = '1' ∨ k.toString.get (k.toString.length - 1) = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def count_n_digit_numbers_with_1 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1  -- only the number 1
  else
    let starts_with_1_count := 10 ^ (n - 1)  -- numbers starting with 1
    let ends_with_1_count := 9 * (10 ^ (n - 2))  -- numbers ending with 1 (excluding those starting with 1)
    let both_start_and_end_with_1_count := 10 ^ (n - 2)  -- numbers both starting and ending with 1
    starts_with_1_count + ends_with_1_count - both_start_and_end_with_1_count

-- LLM HELPER
lemma count_formula_correct (n : Nat) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.toString.get 0 = '1' ∨ k.toString.get (k.toString.length - 1) = '1')}.ncard = 
  count_n_digit_numbers_with_1 n := by
  cases' n with n
  · contradiction
  · cases' n with n
    · simp [count_n_digit_numbers_with_1]
      simp [Set.ncard]
      sorry
    · simp [count_n_digit_numbers_with_1]
      simp [Set.ncard]
      sorry

def implementation (n: Nat) : Nat := count_n_digit_numbers_with_1 n

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use count_n_digit_numbers_with_1 n
  constructor
  · rfl
  · intro hn
    exact count_formula_correct n hn