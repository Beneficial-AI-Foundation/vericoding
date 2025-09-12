/-
  Port of Trab1-Metodos-Formais_tmp_tmp_8fa4trr_circular-array_GetAt.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Size  : Nat :=
  size

def GetAt (i : Nat) : Int :=
  sorry  -- TODO: implement function body

theorem GetAt_spec (i : Nat) (e : Int) :=
  (h_0 : i < size)
  : e == Elements[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks