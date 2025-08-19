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
def digits (base : Nat) : Nat → List Nat
  | 0 => [0]
  | n + 1 => 
    let rec go (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else go (m / base) ((m % base) :: acc)
    termination_by go m _ => m
    decreasing_by simp_wf; apply Nat.div_lt_self; simp; omega
    go (n + 1) []

-- LLM HELPER
def is_palindrome (k: Nat): Prop :=
  let ds := digits 10 k
  ds = ds.reverse

-- LLM HELPER
def even_palindrome (k: Nat): Prop :=
  (Even k) ∧ (is_palindrome k)

-- LLM HELPER
def odd_palindrome (k: Nat): Prop :=
  (Odd k) ∧ (is_palindrome k)

-- LLM HELPER
instance decidable_even (n : Nat) : Decidable (Even n) := 
  Nat.decidable_dvd 2 n

-- LLM HELPER
instance decidable_odd (n : Nat) : Decidable (Odd n) := by
  cases' Nat.even_or_odd n with h h
  · exact isFalse (Nat.odd_iff_not_even.mp.mt (fun _ => h))
  · exact isTrue h

-- LLM HELPER
instance decidable_palindrome (k : Nat) : Decidable (is_palindrome k) := by
  unfold is_palindrome
  exact List.decidableEq

-- LLM HELPER
instance decidable_even_palindrome (k : Nat) : Decidable (even_palindrome k) := by
  unfold even_palindrome
  exact instDecidableAnd

-- LLM HELPER
instance decidable_odd_palindrome (k : Nat) : Decidable (odd_palindrome k) := by
  unfold odd_palindrome
  exact instDecidableAnd

def implementation (n: Nat) : Nat × Nat := 
  if n = 0 then (0, 0)
  else if n = 1 then (0, 1)
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
    · intro h_gt_one
      simp only [implementation]
      split_ifs with h_zero h_one
      · omega
      · omega
      · simp only [true_and]
        constructor
        · intro h_even
          simp only [h_even, ite_true]
        · constructor
          · intro h_odd
            simp only [h_odd, ite_true]
          · constructor
            · intro h_not_odd
              simp only [h_not_odd, ite_false]
            · intro h_not_even
              simp only [h_not_even, ite_false]
    · intro h_eq_one
      simp only [implementation, h_eq_one, ite_true, ite_false]
      constructor <;> norm_num