/-
  Port of vericoding_dafnybench_0436_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MaxArray (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem MaxArray_spec (a : Array Int) (max : Int) :=
  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → a[i]! ≤ max ∧ ∃ i, 0 ≤ i < a.size ∧ a[i]! == max
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks