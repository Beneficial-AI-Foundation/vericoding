/-
  Port of dafny-synthesis_task_id_578_Interleave.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Interleave (s1 : seq<int>) (s2 : seq<int>) (s3 : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem Interleave_spec (s1 : seq<int>) (s2 : seq<int>) (s3 : seq<int>) (r : seq<int>) :=
  (h_0 : |s1| == |s2| ∧ |s2| == |s3|)
  : |r| == 3 * |s1| ∧ ∀ i :: 0 ≤ i < |s1| → r[3*i] == s1[i]! ∧ r[3*i + 1] == s2[i]! ∧ r[3*i + 2] == s3[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks