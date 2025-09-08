/-
In this Kata, you will be given a string and your task is to return the most valuable character. The value of a character is the difference between the index of its last occurrence and the index of its first occurrence. Return the character that has the highest value. If there is a tie, return the alphabetically lowest character. `[For Golang return rune]`

All inputs will be lower case. 

```
For example:
solve('a') = 'a'
solve('ab') = 'a'. Last occurrence is equal to first occurrence of each character. Return lexicographically lowest.
solve("axyzxyz") = 'x'
```

More examples in test cases. Good luck!
-/

def firstIndex (s: String) (c: Char) : Nat :=
  sorry

def lastIndex (s: String) (c: Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve (s: String) : Char :=
  sorry

theorem solve_returns_char_from_input (s: String) (h: s.length > 0) :
  ∃ p: String.Pos, solve s = s.get p :=
  sorry

theorem solve_returns_char_with_minimal_first_last_diff (s: String) (h: s.length > 0) :
  ∀ c: Char, 
  firstIndex s (solve s) - lastIndex s (solve s) 
  ≤ firstIndex s c - lastIndex s c :=
  sorry

theorem solve_returns_lexicographically_first_when_tied (s: String) (h: s.length > 0) :
  ∀ c: Char,
  (firstIndex s c - lastIndex s c = firstIndex s (solve s) - lastIndex s (solve s))
  → solve s ≤ c :=
  sorry

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval solve "a"

/-
info: 'x'
-/
-- #guard_msgs in
-- #eval solve "axyzxyz"

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval solve "dcbadcba"

-- Apps difficulty: introductory
-- Assurance level: unguarded