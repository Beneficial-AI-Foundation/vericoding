/-
  Port of dafny-synthesis_task_id_276_CylinderVolume.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CylinderVolume (radius : Float) (height : Float) : Float :=
  sorry  -- TODO: implement function body

theorem CylinderVolume_spec (radius : Float) (height : Float) (volume : Float) :=
  (h_0 : radius > 0.0)
  (h_1 : height > 0.0)
  : volume == 3.14159265359 * radius * radius * height
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks