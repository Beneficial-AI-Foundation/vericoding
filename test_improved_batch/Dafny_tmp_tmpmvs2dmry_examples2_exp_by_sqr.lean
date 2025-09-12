/-
  Port of Dafny_tmp_tmpmvs2dmry_examples2_exp_by_sqr.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def gcd (m : Nat) (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

def exp (x : Float) (n : Nat) : Float :=
  sorry  -- TODO: implement function body

def exp_by_sqr (x0 : Float) (n0 : Nat) : Float :=
  sorry  -- TODO: implement function body

theorem exp_by_sqr_spec (x0 : Float) (n0 : Nat) (r : Float) :=
  (h_0 : x0 ≥ 0.0;)
  : r == exp(x0, n0);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks