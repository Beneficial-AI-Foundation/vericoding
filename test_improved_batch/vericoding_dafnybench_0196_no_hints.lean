/-
  Port of vericoding_dafnybench_0196_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def InsertionSort (s : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem InsertionSort_spec (s : seq<int>) (r : seq<int>) :=
  : multiset(r) == multiset(s); ∧ IsSorted(r);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks