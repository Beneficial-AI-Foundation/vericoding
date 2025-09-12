/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_ProgramProofs_ch15_QuickSortAux.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : 0 ≤ lo ≤ hi ≤ a.size)
  (h_1 : SplitPoint(a, lo) ∧ SplitPoint(a, hi))
  := by
  sorry  -- TODO: implement proof

def Partition (a : Array Int) (lo : Int) (hi : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Partition_spec (a : Array Int) (lo : Int) (hi : Int) (p : Int) :=
  (h_0 : 0 ≤ lo < hi ≤ a.size)
  (h_1 : SplitPoint(a, lo) ∧ SplitPoint(a, hi))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks