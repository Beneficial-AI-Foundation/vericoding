/-
  Port of vericoding_dafnybench_0557_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def HasCommonElement (a : Array Int) (b : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem HasCommonElement_spec (a : Array Int) (b : Array Int) (result : Bool) :=
  (h_0 : a ≠ null ∧ b ≠ null)
  : result → ∃ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < b.size ∧ a[i]! == b[j]! ∧ !result → ∀ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < b.size → a[i]! ≠ b[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks