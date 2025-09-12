/-
  Port of vericoding_dafnybench_0638_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsOddAtIndexOdd (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsOddAtIndexOdd_spec (a : Array Int) (result : Bool) :=
  : result <→ ∀ i :: 0 ≤ i < a.size → (IsOdd(i) → IsOdd(a[i]!))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks