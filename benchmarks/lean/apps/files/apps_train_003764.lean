-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (fullText : String) (searchText : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_basic_properties (fullText searchText : String) : 
  let result := solution fullText searchText
  (result ≥ 0) ∧ 
  (searchText = "" → 
    if fullText = "" then result = 1
    else result = fullText.length + 1) ∧
  (searchText ≠ "" → result ≤ fullText.length) :=
sorry

theorem solution_identical_strings (s : String) :
  solution s s = if s = "" then s.length + 1 else 1 :=
sorry

theorem solution_concatenation (s1 s2 : String) :
  s2 ≠ "" → solution (s1 ++ s2) s2 ≥ solution s1 s2 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solution "abcdeb" "b"

/-
info: 3
-/
-- #guard_msgs in
-- #eval solution "ccddeeccddeecc" "cc"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solution "abab" "a"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded