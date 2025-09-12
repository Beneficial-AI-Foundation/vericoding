/-
  Port of circular-queue-implemetation_tmp_tmpnulfdc9l_Queue_auxInsertEmptyQueue.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : front == 0 ∧ rear == 0 ∧ circularQueue.size == 0)
  : circularQueue.size == 1 ∧ Content == [item] ∧ |Content| == 1 ∧ rear == 1 ∧ counter == old(counter) + 1 ∧ front == 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks