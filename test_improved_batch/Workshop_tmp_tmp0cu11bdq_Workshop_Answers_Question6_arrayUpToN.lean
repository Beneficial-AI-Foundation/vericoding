/-
  Port of Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question6_arrayUpToN.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def arrayUpToN (n : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem arrayUpToN_spec (n : Int) (a : Array Int) :=
  (h_0 : n ≥ 0)
  : a.size == n ∧ ∀ j :: 0 < j < n → a[j]! ≥ 0 ∧ ∀ j, k : Int :: 0 ≤ j ≤ k < n → a[j]! ≤ a[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks