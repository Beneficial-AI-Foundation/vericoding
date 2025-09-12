/-
  Port of MFS_tmp_tmpmmnu354t_Testes anteriores_T2_ex5_2020_2_leq.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def leq (a : Array Int) (b : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem leq_spec (a : Array Int) (b : Array Int) (result : Bool) :=
  : result <→ (a.size ≤ b.size ∧ a[..] == b[..a.size]) ∨ (∃ k, 0 ≤ k < a.size ∧ k < b.size ∧ a[..k] == b[..k] ∧ a[k]! < b[k]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks