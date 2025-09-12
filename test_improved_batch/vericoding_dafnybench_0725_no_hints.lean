/-
  Port of vericoding_dafnybench_0725_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def buscar (a : Array Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem buscar_spec (a : Array Int) (x : Int) (r : Int) :=
  : r < 0 → ∀ i :: 0 ≤ i <a.size → a[i]! ≠ x ∧ 0 ≤ r < a.size → a[r]! == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks