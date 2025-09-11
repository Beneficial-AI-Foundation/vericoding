-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def missing (indices : List Nat) (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem test_single_index_behavior_no_mission (s : String) (i : Nat) :
  let noSpaces := s.replace " " ""
  i ≥ noSpaces.length →
  missing [i] s = "No mission today" :=
  sorry

theorem test_single_index_behavior_valid (s : String) (i : Nat) :
  let noSpaces := s.replace " " ""
  i < noSpaces.length →
  String.length (missing [i] s) = 1 :=
  sorry

theorem test_space_handling (s : String) :
  missing [0] s = missing [0] (s.replace " " "") :=
  sorry

/-
info: 'ivy'
-/
-- #guard_msgs in
-- #eval missing [5, 0, 3] "I Love You"

/-
info: 'ear'
-/
-- #guard_msgs in
-- #eval missing [7, 10, 1] "see you later"

/-
info: 'No mission today'
-/
-- #guard_msgs in
-- #eval missing [12, 4, 6] "Good Morning"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded