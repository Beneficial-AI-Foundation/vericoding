/-
  Port of Dafny_Programs_tmp_tmp99966ew4_binary_search_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BinarySearch (a : Array Int) (value : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (value : Int) (index : Int) :=
  (h_0 : a ≠ null ∧ 0 ≤ a.size ∧ sorted(a))
  : 0 ≤ index → index < a.size ∧ a[index]! == value ∧ index < 0 → ∀ k :: 0 ≤ k < a.size → a[k]! ≠ value
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks