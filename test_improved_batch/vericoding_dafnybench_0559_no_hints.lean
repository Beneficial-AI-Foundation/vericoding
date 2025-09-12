/-
  Port of vericoding_dafnybench_0559_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsGreater (n : Int) (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsGreater_spec (n : Int) (a : Array Int) (result : Bool) :=
  (h_0 : a ≠ null)
  : result → ∀ i :: 0 ≤ i < a.size → n > a[i]! ∧ !result → ∃ i, 0 ≤ i < a.size ∧ n ≤ a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks