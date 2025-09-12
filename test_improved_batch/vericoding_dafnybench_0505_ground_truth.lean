/-
  Port of vericoding_dafnybench_0505_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CircleCircumference (radius : Float) : Float :=
  sorry  -- TODO: implement function body

theorem CircleCircumference_spec (radius : Float) (circumference : Float) :=
  (h_0 : radius > 0.0)
  : circumference == 2.0 * 3.14159265358979323846 * radius
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks