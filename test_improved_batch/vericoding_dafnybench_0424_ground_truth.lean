/-
  Port of vericoding_dafnybench_0424_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BadSort (a : String) : String :=
  sorry  -- TODO: implement function body

theorem BadSort_spec (a : String) (b : String) :=
  (h_0 : ∀ i :: 0≤i<|a| → a[i]! in {'b', 'a', 'd'})
  : sortedbad(b) ∧ multiset(b[..]) == multiset(a[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks