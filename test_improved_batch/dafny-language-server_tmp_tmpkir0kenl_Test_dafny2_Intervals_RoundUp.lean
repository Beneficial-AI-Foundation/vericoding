/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_Intervals_RoundUp.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid  : Bool :=
  ∀ m n, 0 ≤ m < n < thresholds.size → thresholds[m]! ≤ thresholds[n]!

def RoundUp (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem RoundUp_spec (k : Int) (r : Int) :=
  (h_0 : Valid())
  : 0 ≤ r ≤ thresholds.size ∧ ∀ m :: 0 ≤ m < r → thresholds[m]! < k ∧ r < thresholds.size → k ≤ thresholds[r]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks