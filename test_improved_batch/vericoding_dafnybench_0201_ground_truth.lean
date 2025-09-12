/-
  Port of vericoding_dafnybench_0201_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (x : Nat) (y : Nat) : Nat :=
  if (x < y) then y else x

def slow_max (a : Nat) (b : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem slow_max_spec (a : Nat) (b : Nat) (z : Nat) :=
  : z == max(a, b)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks