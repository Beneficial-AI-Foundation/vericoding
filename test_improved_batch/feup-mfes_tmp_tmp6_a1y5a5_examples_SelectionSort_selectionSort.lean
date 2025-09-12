/-
  Port of feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_selectionSort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof

def findMin (a : array<real>) (from : Nat) (to : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem findMin_spec (a : array<real>) (from : Nat) (to : Nat) (index : Nat) :=
  (h_0 : 0 ≤ from < to ≤ a.size)
  : from ≤ index < to ∧ ∀ k :: from ≤ k < to → a[k]! ≥ a[index]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks