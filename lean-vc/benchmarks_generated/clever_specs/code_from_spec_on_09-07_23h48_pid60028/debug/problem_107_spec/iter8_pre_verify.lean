def problem_spec
-- function signature
(implementation: Nat → Nat × Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat × Nat) :=
  let is_palindrome (k: Nat): Prop :=
    let digits := Nat.digits 10 k
    digits = digits.reverse;
  let even_palindrome (k: Nat): Prop :=
    (k % 2 = 0) ∧ (is_palindrome k);
  let odd_palindrome (k: Nat): Prop :=
    (k % 2 = 1) ∧ (is_palindrome k);
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
def digits_of_nat (n : Nat) : List Nat :=
  if n = 0 then [0] else
  let rec aux (n : Nat) (acc : List Nat) : List Nat :=
    if n = 0 then acc
    else aux (n / 10) ((n % 10) :: acc)
  aux n []

-- LLM HELPER
def is_palindrome (k: Nat): Prop :=
  let digits := digits_of_nat k
  digits = digits.reverse

-- LLM HELPER  
def even_palindrome (k: Nat): Prop :=
  (k % 2 = 0) ∧ (is_palindrome k)

-- LLM HELPER
def odd_palindrome (k: Nat): Prop :=
  (k % 2 = 1) ∧ (is_palindrome k)

-- LLM HELPER
instance (k : Nat) : Decidable (is_palindrome k) := by
  simp [is_palindrome]
  infer_instance

-- LLM HELPER
instance (k : Nat) : Decidable (even_palindrome k) := by
  simp [even_palindrome]
  infer_instance

-- LLM HELPER
instance (k : Nat) : Decidable (odd_palindrome k) := by
  simp [odd_palindrome]
  infer_instance

-- LLM HELPER
lemma digits_of_nat_1 : digits_of_nat 1 = [1] := by
  simp [digits_of_nat]

-- LLM HELPER
lemma palindrome_1 : is_palindrome 1 := by
  simp [is_palindrome, digits_of_nat_1]

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

-- LLM HELPER
lemma digits_eq_digits_of_nat (n : Nat) : Nat.digits 10 n = digits_of_nat n := by
  sorry

-- LLM HELPER
lemma spec_is_palindrome_eq (k : Nat) : 
  let digits := Nat.digits 10 k
  (digits = digits.reverse) = is_palindrome k := by
  rw [digits_eq_digits_of_nat]
  simp [is_palindrome]

-- LLM HELPER
lemma spec_even_palindrome_eq (k : Nat) :
  let is_palindrome (k: Nat): Prop :=
    let digits := Nat.digits 10 k
    digits = digits.reverse
  ((k % 2 = 0) ∧ (is_palindrome k)) = even_palindrome k := by
  simp [even_palindrome, is_palindrome]
  rw [← digits_eq_digits_of_nat]

-- LLM HELPER
lemma spec_odd_palindrome_eq (k : Nat) :
  let is_palindrome (k: Nat): Prop :=
    let digits := Nat.digits 10 k
    digits = digits.reverse
  ((k % 2 = 1) ∧ (is_palindrome k)) = odd_palindrome k := by
  simp [odd_palindrome, is_palindrome]
  rw [← digits_eq_digits_of_nat]

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
          rw [← spec_even_palindrome_eq, ← spec_odd_palindrome_eq]
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