/-
  Port of vericoding_dafnybench_0619_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NthNonagonalNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem NthNonagonalNumber_spec (n : Int) (number : Int) :=
  (h_0 : n ≥ 0)
  : number == n * (7 * n - 5) / 2
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks