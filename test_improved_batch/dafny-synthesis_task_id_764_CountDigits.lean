/-
  Port of dafny-synthesis_task_id_764_CountDigits.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountDigits (s : String) : Int :=
  sorry  -- TODO: implement function body

theorem CountDigits_spec (s : String) (count : Int) :=
  : count ≥ 0 ∧ count == | set i: Int | 0 ≤ i < |s| ∧ IsDigit(s[i]!)|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks