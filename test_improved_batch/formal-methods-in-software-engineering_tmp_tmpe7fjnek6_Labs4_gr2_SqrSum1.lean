/-
  Port of formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs4_gr2_SqrSum1.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SqrSumRec (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def SqrSumBy6 (n : Int) : Int :=
  n * (n + 1) * (2 * n + 1)

def SqrSum1 (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SqrSum1_spec (n : Int) (s : Int) :=
  (h_0 : n ≥ 0)
  : s == SqrSumRec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks