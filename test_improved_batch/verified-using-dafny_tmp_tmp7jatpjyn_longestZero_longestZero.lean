/-
  Port of verified-using-dafny_tmp_tmp7jatpjyn_longestZero_longestZero.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getSize (i : Int) (j : Int) : Int :=
  j - i + 1

def longestZero (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem longestZero_spec (a : Array Int) (sz : Int) :=
  (h_0 : 1 ≤ a.size)
  : 0 ≤ sz ≤ a.size ∧ 0 ≤ pos < a.size ∧ pos + sz ≤ a.size ∧ ∀ i : Int, pos ≤ i < pos + sz → a[i]! == 0 ∧ ∀ i j, (0 ≤ i < j < a.size ∧ getSize(i, j) > sz) → ∃ k, i ≤ k ≤ j ∧ a[k]! ≠ 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks