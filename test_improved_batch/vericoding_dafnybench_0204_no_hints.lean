/-
  Port of vericoding_dafnybench_0204_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def findMax (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem findMax_spec (a : Array Int) (n : Int) (r : Int) :=
  (h_0 : a.size > 0)
  (h_1 : 0 < n ≤ a.size)
  : 0 ≤ r < n ≤ a.size; ∧ ∀ k :: 0 ≤ k < n ≤ a.size → a[r]! ≥ a[k]!; ∧ multiset(a[..]) == multiset(old(a[..]));
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks