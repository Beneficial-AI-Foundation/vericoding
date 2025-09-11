-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vaporcode (s : String) : String := sorry

theorem vaporcode_uppercase (s : String) :
  (vaporcode s).toUpper = vaporcode s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vaporcode_no_consecutive_spaces (s : String) :
  ¬ String.contains (vaporcode s) ' ' := sorry 

theorem vaporcode_preserves_nonspaces (s : String) :
  ((vaporcode s).replace " " "").length = (s.replace " " "").length := sorry

theorem vaporcode_only_original_chars (s : String) (c : Char) :
  c ∈ (vaporcode s).data → (c = ' ' ∨ c ∈ s.toUpper.data) := sorry

theorem vaporcode_spacing (s : String) (h : s.length > 0) :
  (String.splitOn (vaporcode s) "  ").length = (s.replace " " "").length := sorry

theorem vaporcode_empty :
  vaporcode "" = "" := sorry

theorem vaporcode_roundtrip (s : String) :
  ((vaporcode s).replace " " "").toUpper = (s.replace " " "").toUpper := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval vaporcode "Lets go to the movies"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval vaporcode "Why isn"t my code working?"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval vaporcode "Hello World"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded