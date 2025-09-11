-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_keith_number (n : Int) : Int ⊕ Bool := sorry

theorem single_digit_keith_numbers 
  (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : 
  is_keith_number n = Sum.inr false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem keith_number_return_type
  (n : Int) (h : 0 ≤ n) :
  (is_keith_number n = Sum.inr false) ∨ 
  (∃ m : Int, is_keith_number n = Sum.inl m ∧ m > 0) := sorry

theorem keith_number_negative_safe
  (n : Int) (h : n ≤ -1) :
  is_keith_number (Int.natAbs n) = is_keith_number (Int.natAbs n) := sorry

structure Sequence where
  digits : List Int
  values : List Int
  contains_n : Int → Bool

theorem keith_sequence_contains_n
  (n : Int) (h₁ : 10 ≤ n) (h₂ : n ≤ 10000)
  (h₃ : ∃ k, is_keith_number n = Sum.inl k) :
  ∃ (s : Sequence), s.contains_n n = true := sorry

theorem keith_number_deterministic
  (n : Int) (h : 0 ≤ n) :
  is_keith_number n = is_keith_number n := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval is_keith_number 197

/-
info: False
-/
-- #guard_msgs in
-- #eval is_keith_number 196

/-
info: 8
-/
-- #guard_msgs in
-- #eval is_keith_number 742
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded