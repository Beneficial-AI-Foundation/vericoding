/-
  Port of vericoding_dafnybench_0345_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof

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