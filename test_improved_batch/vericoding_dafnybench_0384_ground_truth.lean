/-
  Port of vericoding_dafnybench_0384_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Size  : Nat :=
  size


  (h_0 : !IsFull())
  : Elements == old(Elements) + [e]
  := by
  sorry  -- TODO: implement proof

def Dequeue  : Int :=
  sorry  -- TODO: implement function body

theorem Dequeue_spec (e : Int) :=
  (h_0 : !IsEmpty())
  : Elements == old(Elements)[1..] ∧ e == old(Elements)[0]
  := by
  sorry  -- TODO: implement proof

def GetAt (i : Nat) : Int :=
  sorry  -- TODO: implement function body

theorem GetAt_spec (i : Nat) (e : Int) :=
  (h_0 : i < size)
  : e == Elements[i]!
  := by
  sorry  -- TODO: implement proof

def AsSequence  : seq<int> :=
  sorry  -- TODO: implement function body

theorem AsSequence_spec (s : seq<int>) :=
  : s == Elements
  := by
  sorry  -- TODO: implement proof

def Concatenate (q1 : CircularArray) : CircularArray :=
  sorry  -- TODO: implement function body

theorem Concatenate_spec (q1 : CircularArray) (q2 : CircularArray) :=
  (h_0 : q1.Valid())
  (h_1 : q1 ≠ this)
  : fresh(q2) ∧ q2.Capacity == Capacity + q1.Capacity ∧ q2.Elements == Elements + q1.Elements
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks