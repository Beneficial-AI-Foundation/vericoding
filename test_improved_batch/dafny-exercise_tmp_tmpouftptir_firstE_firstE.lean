/-
  Port of dafny-exercise_tmp_tmpouftptir_firstE_firstE.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def firstE (a : Array Char) : Int :=
  sorry  -- TODO: implement function body

theorem firstE_spec (a : Array Char) (x : Int) :=
  : if 'e' in a[..] then 0 ≤ x < a.size ∧ a[x]! == 'e' ∧ ∀ i | 0 ≤ i < x :: a[i]! ≠ 'e' else x == -1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks