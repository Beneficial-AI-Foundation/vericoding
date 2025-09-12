/-
  Port of Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3_search_findPositionOfIndex_FindPositionOfElement.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindPositionOfElement (a : Array Int) (Element : Nat) (n1 : Nat) (s1 : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem FindPositionOfElement_spec (a : Array Int) (Element : Nat) (n1 : Nat) (s1 : seq<int>) (Position : Int) :=
  (h_0 : n1 == |s1| ∧ 0 ≤ n1 ≤ a.size)
  (h_1 : ∀ i:: 0≤ i < |s1| → a[i]! == s1[i]!)
  : Position == -1 ∨ Position ≥ 1 ∧ |s1| ≠ 0 ∧ Position ≥ 1 → ∃ i, 0 ≤ i < |s1| ∧ s1[i]! == Element
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks