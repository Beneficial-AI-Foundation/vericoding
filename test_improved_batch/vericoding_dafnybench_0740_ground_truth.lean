/-
  Port of vericoding_dafnybench_0740_ground_truth.dfy
  
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

def desenfileira  : Int :=
  sorry  -- TODO: implement function body

theorem desenfileira_spec (e : Int) :=
  (h_0 : |Conteudo| > 0)
  : e == old(Conteudo)[0] ∧ Conteudo == old(Conteudo)[1..]
  := by
  sorry  -- TODO: implement proof

def contem (e : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem contem_spec (e : Int) (r : Bool) :=
  : r <→ ∃ i, 0 ≤ i < cauda ∧ e == a[i]!
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


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks