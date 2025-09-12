/-
  Port of dafny-synthesis_task_id_430_ParabolaDirectrix.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ParabolaDirectrix (a : Float) (h : Float) (k : Float) : Float :=
  sorry  -- TODO: implement function body

theorem ParabolaDirectrix_spec (a : Float) (h : Float) (k : Float) (directrix : Float) :=
  (h_0 : a ≠ 0.0)
  : directrix == k - 1.0 / (4.0 * a)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks