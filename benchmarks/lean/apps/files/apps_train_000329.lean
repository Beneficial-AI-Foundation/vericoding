-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def failure (pattern : String) : List Nat := sorry

def findGoodStrings (n : Nat) (s1 s2 evil : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findGoodStrings_single_char :
  findGoodStrings 1 "a" "a" "b" = 1 := sorry

theorem findGoodStrings_evil_prefix :
  findGoodStrings 4 "abcd" "abcd" "abc" = 0 := sorry

theorem findGoodStrings_full_range :
  findGoodStrings 1 "a" "z" "zz" = 26 := sorry

/-
info: 51
-/
-- #guard_msgs in
-- #eval findGoodStrings 2 "aa" "da" "b"

/-
info: 0
-/
-- #guard_msgs in
-- #eval findGoodStrings 8 "leetcode" "leetgoes" "leet"

/-
info: 2
-/
-- #guard_msgs in
-- #eval findGoodStrings 2 "gx" "gz" "x"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible