/-
  Port of vericoding_dafnybench_0485_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Maximum (values : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem Maximum_spec (values : seq<int>) (max : Int) :=
  (h_0 : values ≠ [])
  : max in values ∧ ∀ i | 0 ≤ i < |values| :: values[i]! ≤ max
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks