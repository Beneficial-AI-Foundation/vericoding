/-
  Port of Trab1-Metodos-Formais_tmp_tmp_8fa4trr_circular-array_Dequeue.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Size  : Nat :=
  size

def Dequeue  : Int :=
  sorry  -- TODO: implement function body

theorem Dequeue_spec (e : Int) :=
  (h_0 : !IsEmpty())
  : Elements == old(Elements)[1..] ∧ e == old(Elements)[0]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks