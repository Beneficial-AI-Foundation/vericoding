/-
  Port of pucrs-metodos-formais-t1_tmp_tmp7gvq3cw4_fila_concat.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def tamanho  : Nat :=
  cauda

def estaVazia  : Bool :=
  sorry  -- TODO: implement complex function body


  : Conteudo == old(Conteudo) + [e]
  := by
  sorry  -- TODO: implement proof

def concat (f2 : Fila) : Fila :=
  sorry  -- TODO: implement function body

theorem concat_spec (f2 : Fila) (r : Fila) :=
  (h_0 : Valid())
  (h_1 : f2.Valid())
  : r.Conteudo == Conteudo + f2.Conteudo
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks