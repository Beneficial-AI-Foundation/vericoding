def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def count_numbers_with_1_at_ends (n: Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else 
    let starts_with_1 := 10 ^ (n - 1)
    let ends_with_1_not_start_1 := 8 * (10 ^ (n - 2))
    starts_with_1 + ends_with_1_not_start_1

def implementation (n: Nat) : Nat := count_numbers_with_1_at_ends n

-- LLM HELPER
lemma single_digit_case (k : ℕ) : 
  10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1') ↔ k = 1 := by
  simp only [pow_zero, pow_one]
  constructor
  · intro h
    cases' h with h1 h2
    cases' h2 with h2 h3
    interval_cases k
    · simp [Nat.repr] at h3
    · rfl
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
    · simp [Nat.repr] at h3
  · intro h
    rw [h]
    simp [Nat.repr]

-- LLM HELPER
lemma multi_digit_structure (n : ℕ) (hn : n > 1) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard = 
  10 ^ (n - 1) + 8 * (10 ^ (n - 2)) := by
  have h_finite : {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.Finite := by
    apply Set.Finite.subset (Set.finite_lt_nat (10 ^ n))
    intro k hk
    exact hk.1.2
  rw [Set.ncard_eq_toFinset_card _ h_finite]
  simp

-- LLM HELPER
lemma count_correct_zero : count_numbers_with_1_at_ends 0 = 0 := by
  simp [count_numbers_with_1_at_ends]

-- LLM HELPER
lemma count_correct_one : 
  count_numbers_with_1_at_ends 1 = {k : ℕ | 10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard := by
  simp [count_numbers_with_1_at_ends]
  have h_finite : {k : ℕ | 10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.Finite := by
    apply Set.Finite.subset (Set.finite_lt_nat (10 ^ 1))
    intro k hk
    exact hk.1.2
  rw [Set.ncard_eq_toFinset_card _ h_finite]
  simp [Set.toFinset_setOf]
  have h_set : {k : ℕ | 10 ^ (1 - 1) ≤ k ∧ k < 10 ^ 1 ∧ (k.repr.front = '1' ∨ k.repr.back = '1')} = {1} := by
    ext k
    rw [single_digit_case]
    simp
  rw [h_set]
  simp

-- LLM HELPER
lemma count_correct_multi (n : ℕ) (hn : n > 1) :
  count_numbers_with_1_at_ends n = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard := by
  simp [count_numbers_with_1_at_ends]
  rw [if_neg (ne_of_gt hn)]
  rw [if_neg (ne_of_gt hn)]
  rw [multi_digit_structure n hn]
  ring

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use count_numbers_with_1_at_ends n
  constructor
  · rfl
  · intro hn_pos
    cases' Nat.eq_zero_or_pos n with h h
    · contradiction
    · cases' h with h h
      · simp [h]
        exact count_correct_one
      · exact count_correct_multi n h