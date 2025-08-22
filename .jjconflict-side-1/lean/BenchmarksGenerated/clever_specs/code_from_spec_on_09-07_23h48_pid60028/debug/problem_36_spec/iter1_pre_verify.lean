def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  (n = 0 → result = 0) ∧
  (0 < n → result = implementation (n - 1) →
    (n % 11 ≠  0 ∧  n % 13 ≠  0) ∨ n.repr.count '7' = 0) ∧
  (0 < n → result ≠ implementation (n - 1) →
    (n % 11 = 0 ∨  n % 13 = 0) ∧
    result - implementation (n - 1) = n.repr.count '7')
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def count_sevens (n: Nat) : Nat :=
  n.repr.count '7'

-- LLM HELPER
def should_add_sevens (n: Nat) : Bool :=
  n % 11 = 0 || n % 13 = 0

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else
    let prev := implementation (n - 1)
    if should_add_sevens n then
      prev + count_sevens n
    else
      prev

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_pos (n: Nat) (h: 0 < n) : 
  implementation n = 
    if should_add_sevens n then 
      implementation (n - 1) + count_sevens n
    else 
      implementation (n - 1) := by
  simp [implementation]
  have : n ≠ 0 := Nat.ne_of_gt h
  simp [this]

-- LLM HELPER
lemma should_add_sevens_iff (n: Nat) : 
  should_add_sevens n = true ↔ n % 11 = 0 ∨ n % 13 = 0 := by
  simp [should_add_sevens, Bool.or_eq_true]

-- LLM HELPER
lemma should_add_sevens_false_iff (n: Nat) : 
  should_add_sevens n = false ↔ n % 11 ≠ 0 ∧ n % 13 ≠ 0 := by
  simp [should_add_sevens, Bool.or_eq_false]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use implementation n
  constructor
  · rfl
  · constructor
    · intro h
      rw [h]
      exact implementation_zero
    · constructor
      · intro h_pos h_eq
        by_cases h_case : should_add_sevens n
        · rw [implementation_pos n h_pos] at h_eq
          rw [if_pos h_case] at h_eq
          have : implementation (n - 1) + count_sevens n = implementation (n - 1) := h_eq
          have : count_sevens n = 0 := by
            rw [← Nat.add_right_cancel this]
          right
          exact this
        · rw [implementation_pos n h_pos] at h_eq
          rw [if_neg h_case] at h_eq
          left
          exact (should_add_sevens_false_iff n).mp h_case
      · intro h_pos h_neq
        by_cases h_case : should_add_sevens n
        · constructor
          · exact (should_add_sevens_iff n).mp h_case
          · rw [implementation_pos n h_pos]
            rw [if_pos h_case]
            simp [count_sevens]
            rw [Nat.add_sub_cancel]
        · rw [implementation_pos n h_pos] at h_neq
          rw [if_neg h_case] at h_neq
          contradiction