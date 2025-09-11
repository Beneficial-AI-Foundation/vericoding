-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lineup_students (input : String) : List String := sorry

/-
  lineupStudentsLengthPreserved:
  For any list of students, the length of the output list
  equals the length of the input list
-/
-- </vc-definitions>

-- <vc-theorems>
theorem lineupStudentsLengthPreserved (input : String) (names : List String) :
  names = lineup_students input → 
  (lineup_students input).length = names.length := sorry

/-
  lineupStudentsSorted:
  For any two adjacent elements in the result,
  if they have equal length then they are reverse alphabetically sorted,
  otherwise the first is longer than the second
-/

theorem lineupStudentsSorted {result : List String} (i : Nat) (h : i + 1 < result.length) :
  let a := result[i]!
  let b := result[i+1]!
  (a.length = b.length → a ≥ b) ∧
  (a.length ≠ b.length → a.length > b.length) := sorry 

/-
  lineupStudentsPreservesElements:
  The output list contains exactly the same elements as the input
-/

theorem lineupStudentsPreservesElements (input : String) (names : List String) :
  names = lineup_students input → 
  ∀ x, (x ∈ names ↔ x ∈ lineup_students input) := sorry

/-
  lineupStudentsSingleElement:
  A single name returns a singleton list with that name
-/

theorem lineupStudentsSingleElement (name : String) :
  lineup_students name = [name] := sorry

/-
  lineupStudentsEmpty:
  An empty string input returns an empty list
-/

theorem lineupStudentsEmpty :
  lineup_students "" = [] := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval lineup_students "Tadashi Takahiro Takao Takashi Takayuki Takehiko Takeo Takeshi Takeshi"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval lineup_students "xxa xxb xxc xxd xa xb xc xd"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval lineup_students "aaa bbb ccc"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded