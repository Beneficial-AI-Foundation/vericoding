-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_exponential_palindromes (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_exp_pal_at_least_one (s : String) :
  s.length > 0 → count_exponential_palindromes s ≥ 1 :=
sorry

theorem count_exp_pal_at_least_length (s : String) :
  s.length > 0 → count_exponential_palindromes s ≥ s.length :=
sorry

theorem count_exp_pal_empty_zero : 
  count_exponential_palindromes "" = 0 :=
sorry

theorem count_exp_pal_single_char (c : Char) :
  count_exponential_palindromes (String.singleton c) = 1 :=
sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval count_exponential_palindromes "11010"

/-
info: 18
-/
-- #guard_msgs in
-- #eval count_exponential_palindromes "101001011"

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_exponential_palindromes "110"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible