/-
  Port of FlexWeek_tmp_tmpc_tfdj_3_ex2_aba.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (a : Int) : Nat :=
  if a < 0 then -a else a

def aba (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem aba_spec (a : Array Int) (b : Array Int) :=
  : a.size == b.size // needed for next line ∧ ∀ x :: 0≤x<b.size → b[x]! == abs(a[x]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks