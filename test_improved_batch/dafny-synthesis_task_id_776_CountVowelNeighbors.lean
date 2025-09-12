/-
  Port of dafny-synthesis_task_id_776_CountVowelNeighbors.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountVowelNeighbors (s : String) : Int :=
  sorry  -- TODO: implement function body

theorem CountVowelNeighbors_spec (s : String) (count : Int) :=
  : count ≥ 0 ∧ count == | set i: Int | 1 ≤ i < |s|-1 ∧ IsVowel(s[i-1]) ∧ IsVowel(s[i+1]) |
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks