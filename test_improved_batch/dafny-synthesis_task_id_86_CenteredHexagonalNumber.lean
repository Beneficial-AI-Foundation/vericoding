/-
  Port of dafny-synthesis_task_id_86_CenteredHexagonalNumber.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CenteredHexagonalNumber (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem CenteredHexagonalNumber_spec (n : Nat) (result : Nat) :=
  (h_0 : n ≥ 0)
  : result == 3 * n * (n - 1) + 1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks