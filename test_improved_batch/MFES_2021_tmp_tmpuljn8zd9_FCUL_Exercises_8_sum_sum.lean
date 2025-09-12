/-
  Port of MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_8_sum_sum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def calcSum (n : Nat) : Nat :=
  n * (n - 1) / 2

def sum (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem sum_spec (n : Nat) (s : Nat) :=
  : s == calcSum(n + 1)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks