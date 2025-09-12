/-
  Port of vericoding_dafnybench_0598_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsArmstrong (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsArmstrong_spec (n : Int) (result : Bool) :=
  (h_0 : 100 ≤ n < 1000)
  : result <→ (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks