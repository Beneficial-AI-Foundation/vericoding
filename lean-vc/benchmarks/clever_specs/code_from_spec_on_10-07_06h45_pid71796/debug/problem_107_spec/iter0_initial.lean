import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

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
  List.Palindrome (Nat.digits 10 k)

-- LLM HELPER
def even_palindrome (k: Nat): Prop :=
  (Even k) ∧ (is_palindrome k)

-- LLM HELPER
def odd_palindrome (k: Nat): Prop :=
  (Odd k) ∧ (is_palindrome k)

-- LLM HELPER
lemma one_is_odd_palindrome : odd_palindrome 1 := by
  constructor
  · exact Nat.odd_iff_not_even.mpr (Nat.not_even_one)
  · simp [is_palindrome]
    rfl

-- LLM HELPER
lemma even_odd_exclusive (k: Nat) : ¬(even_palindrome k ∧ odd_palindrome k) := by
  intro h
  have h_even : Even k := h.1.1
  have h_odd : Odd k := h.2.1
  exact Nat.even_iff_not_odd.mp h_even h_odd

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
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_gt_one
      simp [implementation]
      split_ifs with h_zero h_one
      · contradiction
      · omega
      · simp
        constructor
        · intro h_even
          simp [h_even]
        · constructor
          · intro h_odd
            simp [h_odd]
          · constructor
            · intro h_not_odd
              simp [h_not_odd]
            · intro h_not_even
              simp [h_not_even]
    · intro h_eq_one
      simp [implementation, h_eq_one]
      constructor
      · norm_num
      · norm_num