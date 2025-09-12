/-
  Port of vericoding_dafnybench_0440_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def GetTriple (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem GetTriple_spec (a : Array Int) (index : Int) :=
  : 0 ≤ index < a.size - 2 ∨ index == a.size ∧ index == a.size <→ !triple(a) ∧ 0 ≤ index < a.size - 2 <→ triple(a) ∧ 0 ≤ index < a.size - 2 → a[index]! == a[index + 1] == a[index + 2]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks