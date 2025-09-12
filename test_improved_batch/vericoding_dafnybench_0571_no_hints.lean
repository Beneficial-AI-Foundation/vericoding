/-
  Port of vericoding_dafnybench_0571_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountUppercase (s : String) : Int :=
  sorry  -- TODO: implement function body

theorem CountUppercase_spec (s : String) (count : Int) :=
  : count ≥ 0 ∧ count == | set i: Int | 0 ≤ i < |s| ∧ IsUpperCase(s[i]!)|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks