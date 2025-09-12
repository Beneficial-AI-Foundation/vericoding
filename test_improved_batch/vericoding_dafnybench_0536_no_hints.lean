/-
  Port of vericoding_dafnybench_0536_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ElementWiseSubtraction (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem ElementWiseSubtraction_spec (a : Array Int) (b : Array Int) (result : Array Int) :=
  (h_0 : a ≠ null ∧ b ≠ null)
  (h_1 : a.size == b.size)
  : result ≠ null ∧ result.size == a.size ∧ ∀ i :: 0 ≤ i < result.size → result[i]! == a[i]! - b[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks