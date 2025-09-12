/-
  Port of vericoding_dafnybench_0143_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def AssignmentsToMark (students : Int) (tutors : Int) : Int :=
  sorry  -- TODO: implement function body

theorem AssignmentsToMark_spec (students : Int) (tutors : Int) (r : Int) :=
  (h_0 : students > 0 ∧ tutors > 1)
  : r < students
  := by
  sorry  -- TODO: implement proof

def AssignmentsToMarkOne (students : Int) (tutors : Int) : Int :=
  sorry  -- TODO: implement function body

theorem AssignmentsToMarkOne_spec (students : Int) (tutors : Int) (r : Int) :=
  (h_0 : students > 0 ∧ tutors > 1)
  : r < students
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks