/-
  Port of Clover_linear_search1_LinearSearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LinearSearch (a : Array Int) (e : Int) : Int :=
  sorry  -- TODO: implement function body

theorem LinearSearch_spec (a : Array Int) (e : Int) (n : Int) :=
  : 0≤n≤a.size ∧ n==a.size ∨ a[n]≠=e ∧ ∀ i::0≤i < n → e≠a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks