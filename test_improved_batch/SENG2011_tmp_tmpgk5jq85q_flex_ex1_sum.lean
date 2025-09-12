/-
  Port of SENG2011_tmp_tmpgk5jq85q_flex_ex1_sum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sumcheck (s : Array Int) (i : Int) : Int :=
  sorry  -- TODO: implement complex function body

def sum (s : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem sum_spec (s : Array Int) (a : Int) :=
  (h_0 : s.size > 0)
  : sumcheck(s, s.size) == a
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks