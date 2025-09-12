/-
  Port of vericoding_dafnybench_0659_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MinSecondValueFirst (s : array<seq<int>>) : Int :=
  sorry  -- TODO: implement function body

theorem MinSecondValueFirst_spec (s : array<seq<int>>) (firstOfMinSecond : Int) :=
  (h_0 : s.size > 0)
  (h_1 : ∀ i :: 0 ≤ i < s.size → |s[i]!| ≥ 2)
  : ∃ i, 0 ≤ i < s.size ∧ firstOfMinSecond == s[i]![0] ∧
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks