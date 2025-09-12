/-
  Port of vericoding_dafnybench_0587_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Factorial (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def FactorialOfLastDigit (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem FactorialOfLastDigit_spec (n : Int) (fact : Int) :=
  (h_0 : n ≥ 0)
  : fact == Factorial(n % 10)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks