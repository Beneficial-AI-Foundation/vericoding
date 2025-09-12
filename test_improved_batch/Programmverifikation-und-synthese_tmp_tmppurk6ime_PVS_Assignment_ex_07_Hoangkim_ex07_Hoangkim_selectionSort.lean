/-
  Port of Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_07_Hoangkim_ex07_Hoangkim_selectionSort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindMin (a : Array Int) (lo : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem FindMin_spec (a : Array Int) (lo : Nat) (minIdx : Nat) :=
  (h_0 : a ≠ null ∧ a.size > 0 ∧ lo < a.size)
  : lo ≤ minIdx < a.size ∧ ∀ x :: lo ≤ x < a.size → a[minIdx]! ≤ a[x]!
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks