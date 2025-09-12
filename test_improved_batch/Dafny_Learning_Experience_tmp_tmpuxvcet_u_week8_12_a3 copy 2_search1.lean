/-
  Port of Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3 copy 2_search1.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def search1 (Element : T) : Int :=
  sorry  -- TODO: implement function body

theorem search1_spec (Element : T) (position : Int) :=
  (h_0 : Valid())
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s1| ∧ s1[i]! == Element ∧ !Empty1() ∧ position == -1 → ∀ i :: 0 ≤ i < |s1| → s1[i]! ≠ Element ∨ Empty1() ∧ Valid()
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks