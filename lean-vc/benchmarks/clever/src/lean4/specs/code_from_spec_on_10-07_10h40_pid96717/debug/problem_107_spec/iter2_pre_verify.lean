import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def List.Palindrome (l : List α) : Prop := l = l.reverse

-- LLM HELPER
def Nat.digits (base : Nat) (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rec aux (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else aux (m / base) ((m % base) :: acc)
    aux n []

-- LLM HELPER
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

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
  · use 0
    simp
  · simp [is_palindrome, Nat.digits]
    rfl

-- LLM HELPER
lemma two_is_even_palindrome : even_palindrome 2 := by
  constructor
  · use 1
    simp
  · simp [is_palindrome, Nat.digits]
    rfl

def implementation (n: Nat) : Nat × Nat := 
  if n = 1 then (0, 1)
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
      have h_ne_one : n ≠ 1 := by omega
      simp [h_ne_one]
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
    · intro h_eq_one
      simp [implementation, h_eq_one]