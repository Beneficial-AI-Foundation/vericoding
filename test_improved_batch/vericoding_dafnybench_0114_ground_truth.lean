/-
  Port of vericoding_dafnybench_0114_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function Power(b: nat, n: nat): (p: nat)
  match n case 0 => 1 case 1 => b case _ => b * Power(b, n - 1)

def Log2Floor (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

def boolToNat (b : Bool) : Nat :=
  sorry  -- TODO: implement function body

end DafnyBenchmarks