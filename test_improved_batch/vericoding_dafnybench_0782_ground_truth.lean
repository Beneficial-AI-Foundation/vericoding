/-
  Port of vericoding_dafnybench_0782_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def torneo (Valores : array?<real>) (i : Int) (j : Int) (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem torneo_spec (Valores : array?<real>) (i : Int) (j : Int) (k : Int) (pos_padre : Int) :=
  (h_0 : Valores ≠ null ∧ Valores.size ≥ 20 ∧ Valores.size < 50 ∧ i ≥ 0 ∧ j ≥ 0 ∧ k ≥ 0)
  (h_1 : i < Valores.size ∧ j < Valores.size ∧ k < Valores.size ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i)
  : ∃ p, q, r | p in {i, j, k} ∧ q in {i, j, k} ∧ r in {i, j, k} ∧ p ≠ q ∧ q ≠ r ∧ p ≠ r :: Valores[p]! ≥ Valores[q]! ≥ Valores[r]! ∧ pos_padre == p ∧ pos_madre == q // Q
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks