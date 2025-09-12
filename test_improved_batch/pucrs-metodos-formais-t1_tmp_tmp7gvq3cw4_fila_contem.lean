/-
  Port of pucrs-metodos-formais-t1_tmp_tmp7gvq3cw4_fila_contem.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def tamanho  : Nat :=
  cauda

def estaVazia  : Bool :=
  sorry  -- TODO: implement complex function body

def contem (e : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem contem_spec (e : Int) (r : Bool) :=
  : r <→ ∃ i, 0 ≤ i < cauda ∧ e == a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks