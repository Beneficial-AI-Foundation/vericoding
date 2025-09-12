/-
  Port of dafny-synthesis_task_id_135_NthHexagonalNumber.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NthHexagonalNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem NthHexagonalNumber_spec (n : Int) (hexNum : Int) :=
  (h_0 : n ≥ 0)
  : hexNum == n * ((2 * n) - 1)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks