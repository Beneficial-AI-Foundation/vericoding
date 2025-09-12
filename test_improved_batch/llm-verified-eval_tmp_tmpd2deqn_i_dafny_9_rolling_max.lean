/-
  Port of llm-verified-eval_tmp_tmpd2deqn_i_dafny_9_rolling_max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def isMax (m : Int) (numbers : seq<int>) : Bool :=
  m in numbers ∧ ∀ i :: 0 ≤ i < |numbers| → numbers[i]! ≤ m

def rolling_max (numbers : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem rolling_max_spec (numbers : seq<int>) (result : seq<int>) :=
  (h_0 : numbers ≠ [])
  : |result| == |numbers| ∧ ∀ i :: 0 < i < |result| → isMax(result[i]!, numbers[0..(i+1)])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks