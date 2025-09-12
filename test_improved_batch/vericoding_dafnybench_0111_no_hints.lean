/-
  Port of vericoding_dafnybench_0111_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RecursiveSumDown (str : String) : Int :=
  sorry  -- TODO: implement complex function body

def RecursiveSumUp (str : String) : Int :=
  sorry  -- TODO: implement complex function body


  : ∀ i :: i in offsets → i + |pattern| ≤ |text| ∧ ∀ i :: 0 ≤ i ≤ |text| - |pattern| → (text[i..i+|pattern|] == pattern <→ i in offsets)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks