/-
  Port of dafny-synthesis_task_id_85_SphereSurfaceArea.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SphereSurfaceArea (radius : Float) : Float :=
  sorry  -- TODO: implement function body

theorem SphereSurfaceArea_spec (radius : Float) (area : Float) :=
  (h_0 : radius > 0.0)
  : area == 4.0 * 3.14159265358979323846 * radius * radius
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks