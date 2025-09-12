/-
  Port of vericoding_dafnybench_0441_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Reverse (a : Array Char) : Array Char :=
  sorry  -- TODO: implement function body

theorem Reverse_spec (a : Array Char) (b : Array Char) :=
  (h_0 : a.size > 0)
  : a == old(a) ∧ b.size == a.size ∧ ∀ i :: 0 ≤ i < a.size → b[i]! == a[a.size - i - 1]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks