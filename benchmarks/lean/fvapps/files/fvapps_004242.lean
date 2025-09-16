-- <vc-preamble>
def f (n : Int) : Int :=
  sorry

def is_prime (n : Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_even_digits (n : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem f_result_is_prime (n : Int) (h : n ≥ 2) :
  is_prime (f n) = true ∨ f n = 0 :=
  sorry

theorem f_result_less_than_input (n : Int) (h : n ≥ 2) :
  f n ≤ n :=
  sorry

theorem f_result_has_max_even_digits (n : Int) (h : n ≥ 2) :
  f n ≠ 0 →
  ∀ i : Int, 2 ≤ i → i ≤ n → is_prime i = true →
  count_even_digits i ≤ count_even_digits (f n) :=
  sorry

theorem f_result_largest_for_same_even_digits (n : Int) (h : n ≥ 2) :
  f n ≠ 0 →
  ∀ i : Int, f n < i → i ≤ n → is_prime i = true →
  count_even_digits i = count_even_digits (f n) → False :=
  sorry

theorem f_small_inputs (n : Int) (h : n ≤ 1) :
  f n = 0 :=
  sorry

/-
info: 887
-/
-- #guard_msgs in
-- #eval f 1000

/-
info: 8887
-/
-- #guard_msgs in
-- #eval f 10000

/-
info: 487
-/
-- #guard_msgs in
-- #eval f 500
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded