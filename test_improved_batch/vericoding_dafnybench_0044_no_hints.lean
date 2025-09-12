/-
  Port of vericoding_dafnybench_0044_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Find (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Find_spec (a : Array Int) (key : Int) (index : Int) :=
  : -1≤index<a.size ∧ index≠-1 → a[index]≠=key ∧ (∀ i :: 0 ≤ i < index → a[i]! ≠ key) ∧ index == -1 → (∀ i::0 ≤ i < a.size → a[i]! ≠ key)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks