/-
  Port of circular-queue-implemetation_tmp_tmpnulfdc9l_Queue_remove.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def remove  : Int :=
  sorry  -- TODO: implement function body

theorem remove_spec (item : Int) :=
  (h_0 : front < circularQueue.size)
  (h_1 : circularQueue.size > 0)
  : rear ≤ |old(Content)| ∧ circularQueue.size > 0 ∧ item == old(Content)[old(front)] ∧ front == (old(front) + 1) % circularQueue.size ∧ old(front) < rear → Content == old(Content)[old(front)..rear] ∧ old(front) > rear → Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks