/-
  Port of vericoding_dafnybench_0307_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum_up_to (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def total (a : seq<nat>) : Nat :=
  sorry  -- TODO: implement complex function body

def SumUpTo (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem SumUpTo_spec (n : Nat) (r : Nat) :=
  : r == sum_up_to (n);
  := by
  sorry  -- TODO: implement proof

def Total (a : seq<nat>) : Nat :=
  sorry  -- TODO: implement function body

theorem Total_spec (a : seq<nat>) (r : Nat) :=
  : r == total (a[0..|a|]);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks