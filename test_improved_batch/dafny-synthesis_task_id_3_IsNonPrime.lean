/-
  Port of dafny-synthesis_task_id_3_IsNonPrime.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsNonPrime (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsNonPrime_spec (n : Int) (result : Bool) :=
  (h_0 : n ≥ 2)
  : result <→ (∃ k, 2 ≤ k < n ∧ n % k == 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks