/-
  Port of vericoding_dafnybench_0456_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (a : Array Int) (x : Int) :=
  (h_0 : a.size ≠ 0)
  : 0 ≤ x < a.size ∧ ∀ i :: 0 ≤ i < a.size → a[i]! ≤ a[x]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks