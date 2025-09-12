/-
  Port of vericoding_dafnybench_0363_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Reverse (a : Array Char) : Array Char :=
  sorry  -- TODO: implement function body

theorem Reverse_spec (a : Array Char) (b : Array Char) :=
  (h_0 : a.size > 0)
  : a.size == b.size ∧ ∀ x :: 0 ≤ x < a.size → b[x]! == a[a.size - x - 1]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks