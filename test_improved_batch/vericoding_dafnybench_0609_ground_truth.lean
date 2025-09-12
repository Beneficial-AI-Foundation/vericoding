/-
  Port of vericoding_dafnybench_0609_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindSmallest (s : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindSmallest_spec (s : Array Int) (min : Int) :=
  (h_0 : s.size > 0)
  : ∀ i :: 0 ≤ i < s.size → min ≤ s[i]! ∧ ∃ i, 0 ≤ i < s.size ∧ min == s[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks