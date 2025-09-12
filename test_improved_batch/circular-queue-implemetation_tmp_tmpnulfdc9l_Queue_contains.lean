/-
  Port of circular-queue-implemetation_tmp_tmpnulfdc9l_Queue_contains.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def contains (item : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem contains_spec (item : Int) (contains : Bool) :=
  : contains == true → item in circularQueue[..] ∧ contains == false → item !in circularQueue[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks