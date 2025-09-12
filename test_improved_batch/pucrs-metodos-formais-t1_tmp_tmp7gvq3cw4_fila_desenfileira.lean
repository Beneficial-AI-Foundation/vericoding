/-
  Port of pucrs-metodos-formais-t1_tmp_tmp7gvq3cw4_fila_desenfileira.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def tamanho  : Nat :=
  cauda

def estaVazia  : Bool :=
  sorry  -- TODO: implement complex function body

def desenfileira  : Int :=
  sorry  -- TODO: implement function body

theorem desenfileira_spec (e : Int) :=
  (h_0 : |Conteudo| > 0)
  : e == old(Conteudo)[0] ∧ Conteudo == old(Conteudo)[1..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks