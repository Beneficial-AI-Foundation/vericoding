/-
  Port of vericoding_dafnybench_0545_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ConeVolume (radius : Float) (height : Float) : Float :=
  sorry  -- TODO: implement function body

theorem ConeVolume_spec (radius : Float) (height : Float) (volume : Float) :=
  (h_0 : radius > 0.0 ∧ height > 0.0)
  : volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks