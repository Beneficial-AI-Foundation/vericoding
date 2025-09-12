/-
  Port of dafny-synthesis_task_id_470_PairwiseAddition.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def PairwiseAddition (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem PairwiseAddition_spec (a : Array Int) (result : Array Int) :=
  (h_0 : a ≠ null)
  (h_1 : a.size % 2 == 0)
  : result ≠ null ∧ result.size == a.size / 2 ∧ ∀ i :: 0 ≤ i < result.size → result[i]! == a[2*i] + a[2*i + 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks