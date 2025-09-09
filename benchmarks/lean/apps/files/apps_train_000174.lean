/-
Given a string S and a string T, find the minimum window in S which will contain all the characters in T in complexity O(n).

Example:

Input: S = "ADOBECODEBANC", T = "ABC"
Output: "BANC"

Note:

       If there is no such window in S that covers all characters in T, return the empty string "".
       If there is such window, you are guaranteed that there will always be only one unique minimum window in S.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_window (s t : String) : String := sorry

def verify_contains (window target : String) : Bool := sorry

theorem min_window_empty_target {s : String} : 
  min_window s "" = "" := sorry

theorem min_window_is_substring {s t : String} (h : min_window s t ≠ "") :
  ∃ (i j : Nat), i ≤ j ∧ j ≤ s.length ∧
  min_window s t = s.extract (String.Pos.mk i) (String.Pos.mk j) := sorry

theorem min_window_contains_target {s t : String} (h : min_window s t ≠ "") :
  verify_contains (min_window s t) t = true := sorry

theorem min_window_is_minimal {s t : String} (h : min_window s t ≠ "") :
  ∀ (i j : Nat), i < j → j ≤ (min_window s t).length →
    verify_contains ((min_window s t).extract (String.Pos.mk i) (String.Pos.mk j)) t = false := sorry

theorem min_window_single_char {s t : String} (h1 : t.length = 1) :
  (∃ (i : Nat), i < s.length ∧ s.get (String.Pos.mk i) = t.get (String.Pos.mk 0)) →
  (min_window s t).length = 1 ∧ min_window s t = t := sorry

theorem min_window_length_bounds {s t : String} :
  (min_window s t).length ≤ s.length ∧ 
  (min_window s t ≠ "" → (min_window s t).length ≥ t.data.eraseDups.length) := sorry

/-
info: 'BANC'
-/
-- #guard_msgs in
-- #eval min_window "ADOBECODEBANC" "ABC"

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval min_window "AAAA" "A"

/-
info: ''
-/
-- #guard_msgs in
-- #eval min_window "ABCD" "XY"

-- Apps difficulty: interview
-- Assurance level: unguarded