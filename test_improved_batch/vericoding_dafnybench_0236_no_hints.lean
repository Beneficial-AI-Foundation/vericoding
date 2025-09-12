/-
  Port of vericoding_dafnybench_0236_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof

def isEmpty  : Bool :=
  sorry  -- TODO: implement function body

theorem isEmpty_spec (res : Bool) :=
  : res == Empty()
  := by
  sorry  -- TODO: implement proof

def Peek  : Int :=
  sorry  -- TODO: implement function body

theorem Peek_spec (elem : Int) :=
  (h_0 : Valid() ∧ !Empty())
  : elem == arr[top]!
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def Pop  : Int :=
  sorry  -- TODO: implement function body

theorem Pop_spec (elem : Int) :=
  := by
  sorry  -- TODO: implement proof


  (h_0 : Valid() ∧ !Empty();)
  : Valid(); ∧ ∀ i : Int, 0 ≤ i < capacity - 1 → arr[i]! == old(arr[i + 1]); ∧ top == old(top) - 1;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks