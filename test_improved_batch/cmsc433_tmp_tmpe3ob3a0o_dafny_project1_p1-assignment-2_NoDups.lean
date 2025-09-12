/-
  Port of cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_NoDups.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NoDups (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem NoDups_spec (a : Array Int) (noDups : Bool) :=
  (h_0 : ∀ j : Int, 0 < j < a.size → a[j-1] ≤ a[j]! // a sorted)
  : noDups <→ ∀ j : Int, 1 ≤ j < a.size → a[j-1] ≠ a[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks