/-
  Port of vericoding_dafnybench_0288_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NChoose2 (n : Int) : Int :=
  n * (n - 1) / 2

def SumRange (lo : Int) (hi : Int) : Int :=
  if lo ≥ hi then 0 else SumRange(lo, hi - 1) + hi - 1

def BubbleSort (a : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem BubbleSort_spec (a : Array Int) (n : Nat) :=
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks