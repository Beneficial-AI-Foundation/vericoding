-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>