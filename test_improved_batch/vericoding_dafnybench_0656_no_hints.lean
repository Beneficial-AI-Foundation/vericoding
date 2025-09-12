/-
  Port of vericoding_dafnybench_0656_no_hints.dfy
  
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