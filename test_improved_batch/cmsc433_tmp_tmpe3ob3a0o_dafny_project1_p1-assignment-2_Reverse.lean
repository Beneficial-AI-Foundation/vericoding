/-
  Port of cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_Reverse.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Reverse (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem Reverse_spec (a : Array Int) (aRev : Array Int) :=
  : aRev.size == a.size ∧ ∀ i : Int, 0 ≤ i < a.size → a[i]! == aRev[aRev.size-i-1] ∧ fresh(aRev) // Indicates returned object is newly created in method body
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks