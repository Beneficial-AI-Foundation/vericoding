/-
  Port of llm-verified-eval_tmp_tmpd2deqn_i_dafny_9_max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def isMax (m : Int) (numbers : seq<int>) : Bool :=
  m in numbers ∧ ∀ i :: 0 ≤ i < |numbers| → numbers[i]! ≤ m

def max (numbers : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (numbers : seq<int>) (result : Int) :=
  (h_0 : numbers ≠ [])
  : isMax(result, numbers)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks