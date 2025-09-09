def min_string_length (s : String) : Nat :=
  sorry

-- Result is non-negative

-- <vc-helpers>
-- </vc-helpers>

def reverseString (s : String) : String :=
  sorry

theorem min_string_length_non_negative (s : String) (h : s.length > 0) : 
  min_string_length s ≥ 0 := 
  sorry

-- Result is at most input length

theorem min_string_length_upper_bound (s : String) (h : s.length > 0) :
  min_string_length s ≤ s.length :=
  sorry

-- Single character sequence reduces to at most 1

theorem min_string_length_same_char (s : String) (h : s.length > 0) 
  (h' : ∀ (i j : String.Pos), s.get i = s.get j) :
  min_string_length s ≤ 1 :=
  sorry

-- Palindrome property

theorem min_string_length_palindrome (s : String) (h : s.length > 0) :
  min_string_length s = min_string_length (reverseString s) :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_string_length "abccd"

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_string_length "abbac"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_string_length "aaaa"

-- Apps difficulty: interview
-- Assurance level: guarded