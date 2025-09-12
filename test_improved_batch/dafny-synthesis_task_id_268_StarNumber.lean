/-
  Port of dafny-synthesis_task_id_268_StarNumber.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def StarNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem StarNumber_spec (n : Int) (star : Int) :=
  (h_0 : n ≥ 0)
  : star == 6 * n * (n - 1) + 1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks