/-
  Port of llm-verified-eval_tmp_tmpd2deqn_i_dafny_5_intersperse.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def intersperse (numbers : seq<int>) (delimiter : Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem intersperse_spec (numbers : seq<int>) (delimiter : Int) (interspersed : seq<int>) :=
  : |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0 ∧ ∀ i :: 0 ≤ i < |interspersed| → i % 2 == 0 →
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks