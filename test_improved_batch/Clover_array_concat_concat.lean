/-
  Port of Clover_array_concat_concat.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def concat (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem concat_spec (a : Array Int) (b : Array Int) (c : Array Int) :=
  : c.size==b.size+a.size ∧ ∀ k :: 0 ≤ k < a.size → c[k]! == a[k]! ∧ ∀ k :: 0 ≤ k < b.size → c[k+a.size] == b[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks