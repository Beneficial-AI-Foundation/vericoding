/-
  Port of vericoding_dafnybench_0435_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def firstE (a : Array Char) : Int :=
  sorry  -- TODO: implement function body

theorem firstE_spec (a : Array Char) (x : Int) :=
  : if 'e' in a[..] then 0 ≤ x < a.size ∧ a[x]! == 'e' ∧ ∀ i | 0 ≤ i < x :: a[i]! ≠ 'e' else x == -1
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks