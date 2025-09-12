/-
  Port of vericoding_dafnybench_0580_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SplitStringIntoChars (s : String) : seq<char> :=
  sorry  -- TODO: implement function body

theorem SplitStringIntoChars_spec (s : String) (v : seq<char>) :=
  : |v| == |s| ∧ ∀ i :: 0 ≤ i < |s| → v[i]! == s[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks