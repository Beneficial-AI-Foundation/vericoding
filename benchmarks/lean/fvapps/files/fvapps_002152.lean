-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_palindrome_pairs (strings : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_pairs_non_negative (strings : List String) :
  count_palindrome_pairs strings ≥ 0 :=
  sorry

theorem empty_list_gives_zero :
  count_palindrome_pairs [] = 0 :=
  sorry

theorem singleton_list_gives_zero (s : String) :
  count_palindrome_pairs [s] = 0 :=
  sorry

theorem identical_strings_follow_pattern (s : String) (n : Nat) :
  let strings := List.replicate n s
  count_palindrome_pairs strings = n * (n - 1) / 2 :=
  sorry

theorem empty_strings_pair_with_each_other (n : Nat) :
  let empty_strings := List.replicate n ""
  count_palindrome_pairs empty_strings = n * (n - 1) / 2 :=
  sorry

theorem single_char_strings_pair_with_each_other (n : Nat) :
  let a_strings := List.replicate n "a"
  count_palindrome_pairs a_strings = n * (n - 1) / 2 :=
  sorry
-- </vc-theorems>