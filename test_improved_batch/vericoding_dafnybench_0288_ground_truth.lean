/-
  Port of vericoding_dafnybench_0288_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NChoose2 (n : Int) : Int :=
  n * (n - 1) / 2

def SumRange (lo : Int) (hi : Int) : Int :=
  sorry  -- TODO: implement function body

def BubbleSort (a : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem BubbleSort_spec (a : Array Int) (n : Nat) :=
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks