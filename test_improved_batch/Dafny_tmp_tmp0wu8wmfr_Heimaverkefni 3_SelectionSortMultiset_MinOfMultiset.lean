/-
  Port of Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 3_SelectionSortMultiset_MinOfMultiset.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MinOfMultiset (m : multiset<int>) : Int :=
  sorry  -- TODO: implement function body

theorem MinOfMultiset_spec (m : multiset<int>) (min : Int) :=
  (h_0 : m ≠ multiset{};)
  : min in m; ∧ ∀ z | z in m :: min ≤ z;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks