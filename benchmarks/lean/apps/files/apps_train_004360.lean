-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_anagram (s1 s2: String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_anagram_symmetry (s1 s2 : String) :
  is_anagram s1 s2 = is_anagram s2 s1 := by
  sorry

theorem is_anagram_reflexive (s : String) :
  is_anagram s s = true := by
  sorry

theorem different_length_not_anagrams (s1 s2 : String) :
  s1.length ≠ s2.length → is_anagram s1 s2 = false := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_anagram "foefet" "toffee"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_anagram "Buckethead" "DeathCubeK"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_anagram "dumble" "bumble"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded