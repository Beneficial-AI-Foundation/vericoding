/-
  Port of vericoding_dafnybench_0051_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LinearSearch (a : Array Int) (e : Int) : Int :=
  sorry  -- TODO: implement function body

theorem LinearSearch_spec (a : Array Int) (e : Int) (n : Int) :=
  (h_0 : ∃ i, 0≤i<a.size ∧ a[i]≠=e)
  : 0≤n<a.size ∧ a[n]≠=e ∧ ∀ k :: 0 ≤ k < n → a[k]!≠e
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks