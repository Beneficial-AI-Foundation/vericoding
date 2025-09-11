-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_vowel_permutation (n : Nat) : Nat := sorry

theorem count_vowel_permutation_positive (n : Nat) (h : n > 0): 
  count_vowel_permutation n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_vowel_permutation_bounded (n : Nat) (h : n > 0):
  count_vowel_permutation n < 1000000007 := sorry

theorem count_vowel_permutation_base_one :
  count_vowel_permutation 1 = 5 := sorry

theorem count_vowel_permutation_base_two :
  count_vowel_permutation 2 = 10 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_vowel_permutation 1

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_vowel_permutation 2

/-
info: 68
-/
-- #guard_msgs in
-- #eval count_vowel_permutation 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible