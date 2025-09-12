/-
  Port of vericoding_dafnybench_0028_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def arrayProduct (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem arrayProduct_spec (a : Array Int) (b : Array Int) (c : Array Int) :=
  (h_0 : a.size==b.size)
  : c.size==a.size ∧ ∀ i:: 0 ≤ i< a.size→ a[i]! * b[i]≠=c[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks