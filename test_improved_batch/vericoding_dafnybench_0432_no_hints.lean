/-
  Port of vericoding_dafnybench_0432_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def appendArray (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem appendArray_spec (a : Array Int) (b : Array Int) (c : Array Int) :=
  : c.size == a.size + b.size ∧ ∀ i :: 0 ≤ i < a.size → a[i]! == c[i]! ∧ ∀ i :: 0 ≤ i < b.size → b[i]! == c[a.size + i]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks