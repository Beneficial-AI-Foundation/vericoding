/-
  Port of vericoding_dafnybench_0684_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def pow (n : Nat) (alpha : Float) : Float :=
  sorry  -- TODO: implement function body

theorem pow_spec (n : Nat) (alpha : Float) (product : Float) :=
  (h_0 : n > 0)
  (h_1 : alpha > 0.0)
  : product == power(n as real, alpha)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks