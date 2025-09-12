/-
  Port of vericoding_dafnybench_0495_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getWeightsOfAllRightChildren  : Nat :=
  sorry  -- TODO: implement function body

def length  : Nat :=
  this.weight + getWeightsOfAllRightChildren()

def report (i : Nat) (j : Nat) : String :=
  sorry  -- TODO: implement function body

theorem report_spec (i : Nat) (j : Nat) (s : String) :=
  (h_0 : 0 ≤ i ≤ j ≤ |this.Contents|)
  (h_1 : Valid())
  : s == this.Contents[i..j]
  := by
  sorry  -- TODO: implement proof

def toString  : String :=
  sorry  -- TODO: implement function body

theorem toString_spec (s : String) :=
  (h_0 : Valid())
  : s == Contents
  := by
  sorry  -- TODO: implement proof

def getCharAtIndex (index : Nat) : Char :=
  sorry  -- TODO: implement function body

theorem getCharAtIndex_spec (index : Nat) (c : Char) :=
  (h_0 : Valid() ∧ 0 ≤ index < |Contents|)
  : c == Contents[index]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks