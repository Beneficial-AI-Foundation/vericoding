/-
  Port of dafny-synthesis_task_id_424_ExtractRearChars.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ExtractRearChars (l : seq<string>) : seq<char> :=
  sorry  -- TODO: implement function body

theorem ExtractRearChars_spec (l : seq<string>) (r : seq<char>) :=
  (h_0 : ∀ i :: 0 ≤ i < |l| → |l[i]!| > 0)
  : |r| == |l| ∧ ∀ i :: 0 ≤ i < |l| → r[i]! == l[i]![|l[i]!| - 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks