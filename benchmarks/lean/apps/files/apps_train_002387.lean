-- <vc-helpers>
-- </vc-helpers>

def find_longest_uncommon_subsequence (s1 s2 : String) : Int := sorry

theorem identical_strings_property (s1 s2 : String) (h1 : s1.length > 0) (h2 : s2.length > 0) :
  (s1 = s2 → find_longest_uncommon_subsequence s1 s2 = -1) ∧ 
  (s1 ≠ s2 → find_longest_uncommon_subsequence s1 s2 = max s1.length s2.length) := sorry

theorem symmetry_property (s1 s2 : String) (h1 : s1.length > 0) (h2 : s2.length > 0) :
  find_longest_uncommon_subsequence s1 s2 = find_longest_uncommon_subsequence s2 s1 := sorry

theorem same_string_property (s : String) (h : s.length > 0) :
  find_longest_uncommon_subsequence s s = -1 := sorry

theorem return_value_bounds (s1 s2 : String) (h1 : s1.length > 0) (h2 : s2.length > 0) :
  let result := find_longest_uncommon_subsequence s1 s2
  result = -1 ∨ result ≥ max s1.length s2.length := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_longest_uncommon_subsequence "aba" "cdc"

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_longest_uncommon_subsequence "aaa" "aaa"

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_longest_uncommon_subsequence "aefawf" "aefawf"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible