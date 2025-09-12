/-
  Port of vericoding_dafnybench_0535_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NthDecagonalNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem NthDecagonalNumber_spec (n : Int) (decagonal : Int) :=
  (h_0 : n ≥ 0)
  : decagonal == 4 * n * n - 3 * n
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks