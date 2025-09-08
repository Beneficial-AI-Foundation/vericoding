/-
**This Kata is intended as a small challenge for my students**

All Star Code Challenge #18

Create a function called that accepts 2 string arguments and returns an integer of the count of occurrences the 2nd argument is found in the first one.

If no occurrences can be found, a count of 0 should be returned.

Notes:
* The first argument can be an empty string  
* The second string argument will always be of length 1
-/

-- <vc-helpers>
-- </vc-helpers>

def strCount (s : String) (letter : Char) : Nat :=
  sorry

theorem strCount_nonnegative (s : String) (letter : Char) :
  strCount s letter ≥ 0 :=
sorry

theorem strCount_upper_bound (s : String) (letter : Char) :
  strCount s letter ≤ s.length :=
sorry

theorem strCount_matches_actual (s : String) (letter : Char) :
  strCount s letter = (s.data.filter (· = letter)).length :=
sorry

theorem strCount_empty (letter : Char) :
  strCount "" letter = 0 :=
sorry

theorem strCount_all_same (s : String) (letter : Char) :
  s.length > 0 → (∀ c ∈ s.data, c = letter) → strCount s letter = s.length :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval str_count "hello" "l"

/-
info: 5
-/
-- #guard_msgs in
-- #eval str_count "ggggg" "g"

/-
info: 2
-/
-- #guard_msgs in
-- #eval str_count "hello world" "o"

-- Apps difficulty: introductory
-- Assurance level: guarded