/-
You are given two strings s1 and s2 of equal length consisting of letters "x" and "y" only. Your task is to make these two strings equal to each other. You can swap any two characters that belong to different strings, which means: swap s1[i] and s2[j].
Return the minimum number of swaps required to make s1 and s2 equal, or return -1 if it is impossible to do so.

Example 1:
Input: s1 = "xx", s2 = "yy"
Output: 1
Explanation: 
Swap s1[0] and s2[1], s1 = "yx", s2 = "yx".
Example 2: 
Input: s1 = "xy", s2 = "yx"
Output: 2
Explanation: 
Swap s1[0] and s2[0], s1 = "yy", s2 = "xx".
Swap s1[0] and s2[1], s1 = "xy", s2 = "xy".
Note that you can't swap s1[0] and s1[1] to make s1 equal to "yx", cause we can only swap chars in different strings.
Example 3:
Input: s1 = "xx", s2 = "xy"
Output: -1

Example 4:
Input: s1 = "xxyyxyxyxx", s2 = "xyyxyxxxyx"
Output: 4

Constraints:

1 <= s1.length, s2.length <= 1000
s1, s2 only contain 'x' or 'y'.
-/

-- <vc-helpers>
-- </vc-helpers>

def minimumSwap (s1 s2 : List XY) : Int := sorry

theorem string_length_equal (s1 s2 : List XY) :
  minimumSwap s1 s2 ≠ -1 → s1.length = s2.length := sorry

theorem result_bounds (s1 s2 : List XY) : 
  let result := minimumSwap s1 s2
  result ≠ -1 → 0 ≤ result ∧ result ≤ s1.length := sorry

theorem invalid_case_parity (s1 s2 : List XY) :
  let xy := (List.zip s1 s2).filter (fun p => decide (p.1 = XY.x) && decide (p.2 = XY.y)) |>.length
  let yx := (List.zip s1 s2).filter (fun p => decide (p.1 = XY.y) && decide (p.2 = XY.x)) |>.length
  (xy + yx) % 2 = 1 → minimumSwap s1 s2 = -1 := sorry

theorem identical_strings_no_swaps (s : List XY) :
  minimumSwap s s = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval minimumSwap "xx" "yy"

/-
info: 2
-/
-- #guard_msgs in
-- #eval minimumSwap "xy" "yx"

/-
info: -1
-/
-- #guard_msgs in
-- #eval minimumSwap "xx" "xy"

-- Apps difficulty: interview
-- Assurance level: guarded