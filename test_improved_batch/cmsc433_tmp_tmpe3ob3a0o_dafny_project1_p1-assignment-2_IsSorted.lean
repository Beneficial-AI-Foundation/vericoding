/-
  Port of cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_IsSorted.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsSorted (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsSorted_spec (a : Array Int) (isSorted : Bool) :=
  : isSorted <→ ∀ j : Int, 1 ≤ j < a.size → a[j-1] ≤ a[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks