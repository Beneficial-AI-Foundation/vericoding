/-
  Port of Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 3_InsertionSortMultiset_Sort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Search (s : seq<int>) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search_spec (s : seq<int>) (x : Int) (k : Int) :=
  := by
  sorry  -- TODO: implement proof

def Sort (m : multiset<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem Sort_spec (m : multiset<int>) (r : seq<int>) :=
  : multiset(r) == m; ∧ ∀ p,q | 0 ≤ p < q < |r| :: r[p]! ≤ r[q]!;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks