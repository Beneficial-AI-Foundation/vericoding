def max_vowels (s : String) (k : Nat) : Nat := sorry

def count_vowels (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def is_vowel (c : Char) : Bool := sorry

theorem max_vowels_monotonic {s : String} {k : Nat}
  (h1 : k < String.length s) :
  max_vowels s k ≤ max_vowels s (k + 1) := sorry

theorem max_vowels_empty {k : Nat}
  (h1 : k > 0) :
  max_vowels "" k = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_vowels "abciiidef" 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_vowels "leetcode" 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_vowels "rhythms" 4

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible