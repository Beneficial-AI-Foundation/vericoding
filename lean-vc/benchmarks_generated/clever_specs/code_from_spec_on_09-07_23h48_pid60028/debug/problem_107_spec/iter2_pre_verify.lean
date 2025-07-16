def problem_spec
-- function signature
(implementation: Nat → Nat × Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat × Nat) :=
  let is_palindrome (k: Nat): Prop :=
    List.Palindrome (Nat.digits 10 k);
  let even_palindrome (k: Nat): Prop :=
    (Even k) ∧ (is_palindrome k);
  let odd_palindrome (k: Nat): Prop :=
    (Odd k) ∧ (is_palindrome k);
  n > 0 →
  (1 < n →
    let impl_n_minus_1 := implementation (n - 1);
    ((even_palindrome n) → result.1 = 1 + impl_n_minus_1.1) ∧
    ((odd_palindrome n) → result.2 = 1 + impl_n_minus_1.2) ∧
    (¬ (odd_palindrome n) → result.2 = impl_n_minus_1.2) ∧
    (¬ (even_palindrome n) → result.1 = impl_n_minus_1.1))
  ∧
  (n = 1 → (result.1 = 0) ∧ (result.2 = 1));
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def is_palindrome (k: Nat): Prop :=
  let digits := Nat.digits 10 k
  digits = digits.reverse

-- LLM HELPER  
def even_palindrome (k: Nat): Prop :=
  (k % 2 = 0) ∧ (is_palindrome k)

-- LLM HELPER
def odd_palindrome (k: Nat): Prop :=
  (k % 2 = 1) ∧ (is_palindrome k)

-- LLM HELPER
instance : Decidable (is_palindrome k) := by
  simp [is_palindrome]
  infer_instance

-- LLM HELPER
instance : Decidable (even_palindrome k) := by
  simp [even_palindrome]
  infer_instance

-- LLM HELPER
instance : Decidable (odd_palindrome k) := by
  simp [odd_palindrome]
  infer_instance

-- LLM HELPER
lemma palindrome_1 : is_palindrome 1 := by
  simp [is_palindrome, Nat.digits]

-- LLM HELPER
lemma odd_1 : 1 % 2 = 1 := by norm_num

-- LLM HELPER
lemma odd_palindrome_1 : odd_palindrome 1 := by
  constructor
  · exact odd_1
  · exact palindrome_1

-- LLM HELPER
lemma not_even_palindrome_1 : ¬even_palindrome 1 := by
  intro h
  cases h with
  | mk h_even h_pal =>
    simp at h_even

def implementation (n: Nat) : Nat × Nat :=
  if n = 1 then (0, 1)
  else if n = 0 then (0, 0)
  else
    let prev := implementation (n - 1)
    let even_count := if even_palindrome n then prev.1 + 1 else prev.1
    let odd_count := if odd_palindrome n then prev.2 + 1 else prev.2
    (even_count, odd_count)

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_gt_1
      simp [implementation]
      split
      · contradiction
      · split
        · omega
        · simp
          constructor
          · intro h_even_pal
            simp [h_even_pal]
          · constructor
            · intro h_odd_pal
              simp [h_odd_pal]
            · constructor
              · intro h_not_odd_pal
                simp [h_not_odd_pal]
              · intro h_not_even_pal
                simp [h_not_even_pal]
    · intro h_eq_1
      simp [implementation, h_eq_1]