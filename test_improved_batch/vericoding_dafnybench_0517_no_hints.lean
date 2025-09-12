/-
  Port of vericoding_dafnybench_0517_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ReplaceBlanksWithChar (s : String) (ch : Char) : String :=
  sorry  -- TODO: implement function body

theorem ReplaceBlanksWithChar_spec (s : String) (ch : Char) (v : String) :=
  : |v| == |s| ∧ ∀ i :: 0 ≤ i < |s| → (s[i]! == ' ' → v[i]! == ch) ∧ (s[i]! ≠ ' ' → v[i]! == s[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks