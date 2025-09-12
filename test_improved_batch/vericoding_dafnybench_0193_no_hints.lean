/-
  Port of vericoding_dafnybench_0193_no_hints.dfy
  
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


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def Sort (m : multiset<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem Sort_spec (m : multiset<int>) (s : seq<int>) :=
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks