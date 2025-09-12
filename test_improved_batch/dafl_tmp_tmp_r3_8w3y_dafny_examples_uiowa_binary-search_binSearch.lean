/-
  Port of dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_binary-search_binSearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def binSearch (a : Array Int) (K : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem binSearch_spec (a : Array Int) (K : Int) (b : Bool) :=
  (h_0 : isSorted(a))
  : b == ∃ i:nat :: i < a.size ∧ a[i]! == K
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks