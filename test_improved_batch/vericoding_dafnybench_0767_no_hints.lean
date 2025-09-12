/-
  Port of vericoding_dafnybench_0767_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Tangent (r : Array Int) (x : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Tangent_spec (r : Array Int) (x : Array Int) (b : Bool) :=
  (h_0 : ∀ i, j :: 0 ≤ i ≤ j < x.size → x[i]! ≤ x[j]! // values in x will be in ascending order or empty)
  (h_1 : ∀ i, j :: (0 ≤ i < r.size ∧ 0 ≤ j < x.size) → (r[i]! ≥ 0 ∧ x[j]! ≥ 0)       // x and r will contain no negative values)
  : !b → ∀ i, j :: 0 ≤ i< r.size ∧ 0 ≤ j < x.size → r[i]! ≠ x[j]! ∧ b → ∃ i, j :: 0 ≤ i< r.size ∧ 0 ≤ j < x.size ∧ r[i]! == x[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks