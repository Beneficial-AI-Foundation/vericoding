/-
  Port of dafny-synthesis_task_id_17_SquarePerimeter.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SquarePerimeter (side : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SquarePerimeter_spec (side : Int) (perimeter : Int) :=
  (h_0 : side > 0)
  : perimeter == 4 * side
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks