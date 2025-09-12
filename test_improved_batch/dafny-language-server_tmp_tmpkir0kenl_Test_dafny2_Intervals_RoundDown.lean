/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_Intervals_RoundDown.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid  : Bool :=
  ∀ m n, 0 ≤ m < n < thresholds.size → thresholds[m]! ≤ thresholds[n]!

def RoundDown (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem RoundDown_spec (k : Int) (r : Int) :=
  (h_0 : Valid())
  : -1 ≤ r < thresholds.size ∧ ∀ m :: r < m < thresholds.size → k < thresholds[m]! ∧ 0 ≤ r → thresholds[r]! ≤ k
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks