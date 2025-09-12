/-
  Port of vericoding_dafnybench_0722_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<int>) (n : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def below_zero (ops : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem below_zero_spec (ops : seq<int>) (result : Bool) :=
  : result <→ ∃ n: nat :: n ≤ |ops| ∧ sum(ops, n) < 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks