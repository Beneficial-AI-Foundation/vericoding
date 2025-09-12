/-
  Port of vericoding_dafnybench_0635_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Difference (a : seq<int>) (b : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem Difference_spec (a : seq<int>) (b : seq<int>) (diff : seq<int>) :=
  : ∀ x :: x in diff <→ (x in a ∧ x !in b) ∧ ∀ i, j :: 0 ≤ i < j < |diff| → diff[i]! ≠ diff[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks