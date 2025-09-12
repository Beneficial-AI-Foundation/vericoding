/-
  Port of dafny-synthesis_task_id_14_TriangularPrismVolume.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def TriangularPrismVolume (base : Int) (height : Int) (length : Int) : Int :=
  sorry  -- TODO: implement function body

theorem TriangularPrismVolume_spec (base : Int) (height : Int) (length : Int) (volume : Int) :=
  (h_0 : base > 0)
  (h_1 : height > 0)
  (h_2 : length > 0)
  : volume == (base * height * length) / 2
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks