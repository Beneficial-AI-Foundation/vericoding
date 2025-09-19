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
-- </vc-theorems>