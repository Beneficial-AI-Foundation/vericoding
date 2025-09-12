/-
  Port of formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs4_gr2_DivMod1.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SqrSumRec (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def SqrSumBy6 (n : Int) : Int :=
  n * (n + 1) * (2 * n + 1)

def DivMod1 (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem DivMod1_spec (a : Int) (b : Int) (q : Int) :=
  (h_0 : b > 0 ∧ a ≥ 0)
  : a == b*q + r ∧ 0 ≤ r < b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks