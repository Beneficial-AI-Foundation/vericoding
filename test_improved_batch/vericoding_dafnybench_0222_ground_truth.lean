/-
  Port of vericoding_dafnybench_0222_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Max (a : array<nat>) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (a : array<nat>) (m : Int) :=
  : a.size > 0 → ∀ k :: 0≤k<a.size → m ≥ a[k]!// not strong enough ∧ a.size == 0 → m == -1 ∧ a.size > 0 → m in a[..] // finally at the top // approach did not work for recusrive function
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks