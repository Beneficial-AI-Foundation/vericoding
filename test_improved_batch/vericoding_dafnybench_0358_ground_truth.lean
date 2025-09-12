/-
  Port of vericoding_dafnybench_0358_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Symmetric (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Symmetric_spec (a : Array Int) (flag : Bool) :=
  : flag == true → ∀ x :: 0 ≤ x < a.size → a[x]! == a[a.size - x - 1] ∧ flag == false → ∃ x, 0 ≤ x < a.size ∧ a[x]! ≠ a[a.size - x - 1]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks