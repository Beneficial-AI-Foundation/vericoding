/-
  Port of vericoding_dafnybench_0499_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def AppendArrayToSeq (s : seq<int>) (a : Array Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem AppendArrayToSeq_spec (s : seq<int>) (a : Array Int) (r : seq<int>) :=
  (h_0 : a ≠ null)
  : |r| == |s| + a.size ∧ ∀ i :: 0 ≤ i < |s| → r[i]! == s[i]! ∧ ∀ i :: 0 ≤ i < a.size → r[|s| + i] == a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks