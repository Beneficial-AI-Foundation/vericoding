/-
  Port of vericoding_dafnybench_0716_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def ComputeFib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem ComputeFib_spec (n : Nat) (b : Nat) :=
  : b == fib(n)  // Do not change this postcondition
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks