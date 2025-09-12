/-
  Port of Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3 copy 2_search3.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def search3 (Element : T) : Int :=
  sorry  -- TODO: implement function body

theorem search3_spec (Element : T) (position : Int) :=
  (h_0 : Valid())
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s2| ∧ s2[i]! == Element ∧ !Empty2()
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks