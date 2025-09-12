/-
  Port of dafny-synthesis_task_id_126_SumOfCommonDivisors.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumOfCommonDivisors (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumOfCommonDivisors_spec (a : Int) (b : Int) (sum : Int) :=
  (h_0 : a > 0 ∧ b > 0)
  : sum ≥ 0 ∧ ∀ d :: 1 ≤ d ≤ a ∧ 1 ≤ d ≤ b ∧ a % d == 0 ∧ b % d == 0 → sum ≥ d
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks