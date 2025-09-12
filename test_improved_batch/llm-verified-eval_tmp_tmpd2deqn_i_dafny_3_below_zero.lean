/-
  Port of llm-verified-eval_tmp_tmpd2deqn_i_dafny_3_below_zero.dfy
  
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