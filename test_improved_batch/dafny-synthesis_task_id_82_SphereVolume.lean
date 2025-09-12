/-
  Port of dafny-synthesis_task_id_82_SphereVolume.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SphereVolume (radius : Float) : Float :=
  sorry  -- TODO: implement function body

theorem SphereVolume_spec (radius : Float) (volume : Float) :=
  (h_0 : radius > 0.0)
  : volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks