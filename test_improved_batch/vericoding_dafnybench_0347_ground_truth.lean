/-
  Port of vericoding_dafnybench_0347_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Gauss (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Gauss_spec (n : Int) (sum : Int) :=
  (h_0 : n ≥ 0)
  : sum == n*(n+1)/2     //
  := by
  sorry  -- TODO: implement proof

def sumOdds (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem sumOdds_spec (n : Nat) (sum : Nat) :=
  : sum == n*n;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks