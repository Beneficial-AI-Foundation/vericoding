/-
Gigi is a clever monkey, living in the zoo, his teacher (animal keeper) recently taught him some knowledge of "0".

In Gigi's eyes, "0" is a character contains some circle(maybe one, maybe two).

So, a is a "0",b is a "0",6 is also a "0"，and 8 have two "0" ,etc...

Now, write some code to count how many "0"s in the text.

Let us see who is smarter? You ? or monkey?

Input always be a string(including words numbers and symbols)，You don't need to verify it, but pay attention to the difference between uppercase and lowercase letters.

Here is a table of characters：

one zeroabdegopq069DOPQR         () <-- A pair of braces as a zerotwo zero%&B8

Output will be a number of "0".
-/

-- <vc-helpers>
-- </vc-helpers>

def count_zeros (s: String) : Nat :=
  sorry

theorem count_zeros_nonnegative (s: String) :
  count_zeros s ≥ 0 := sorry

theorem count_zeros_upper_bound (s: String) :
  count_zeros s ≤ 2 * s.length := sorry

theorem count_zeros_concatenation (s: String) :
  count_zeros (s ++ s) = count_zeros s * 2 := sorry

theorem count_zeros_case_insensitive (c: Char) :
  c ∈ ['d', 'o', 'p', 'q'] →
  count_zeros (String.mk [c]) = count_zeros (String.mk [c.toUpper]) := sorry

theorem count_zeros_parentheses :
  count_zeros "()" = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_zeros ""

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_zeros "0oO0oO"

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_zeros "abcdefghijklmnopqrstuvwxyz"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible