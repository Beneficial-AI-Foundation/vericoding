/-
  Port of circular-queue-implemetation_tmp_tmpnulfdc9l_Queue_auxInsertEndQueue.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : front == 0 ∧ rear == circularQueue.size ∧ circularQueue.size ≥ 1)
  : Content == old(Content) + [item] ∧ |Content| == old(|Content|) + 1 ∧ front == 0 ∧ rear == old(rear) + 1 ∧ counter == old(counter) + 1
  := by
  sorry  -- TODO: implement proof


  (h_0 : rear < front ∧ front < circularQueue.size)
  : rear == old(rear) + 1 ∧ counter == old(counter) + 1 ∧ Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.size]) ∧ |Content| == old(|Content|) + 1
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def remove  : Int :=
  sorry  -- TODO: implement function body

theorem remove_spec (item : Int) :=
  (h_0 : front < circularQueue.size)
  (h_1 : circularQueue.size > 0)
  : rear ≤ |old(Content)| ∧ circularQueue.size > 0 ∧ item == old(Content)[old(front)] ∧ front == (old(front) + 1) % circularQueue.size ∧ old(front) < rear → Content == old(Content)[old(front)..rear] ∧ old(front) > rear → Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks