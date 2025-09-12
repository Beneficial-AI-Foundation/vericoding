/-
  Port of vericoding_dafnybench_0008_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<int>) (n : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def BelowZero (ops : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem BelowZero_spec (ops : seq<int>) (result : Bool) :=
  : result <→ ∃ n: nat :: n ≤ |ops| ∧ sum(ops, n) < 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks