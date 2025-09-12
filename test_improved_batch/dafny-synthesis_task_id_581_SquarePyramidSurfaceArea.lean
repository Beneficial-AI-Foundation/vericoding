/-
  Port of dafny-synthesis_task_id_581_SquarePyramidSurfaceArea.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SquarePyramidSurfaceArea (baseEdge : Int) (height : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SquarePyramidSurfaceArea_spec (baseEdge : Int) (height : Int) (area : Int) :=
  (h_0 : baseEdge > 0)
  (h_1 : height > 0)
  : area == baseEdge * baseEdge + 2 * baseEdge * height
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks