/-
  Port of vericoding_dafnybench_0138_no_hints.dfy
  
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


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks