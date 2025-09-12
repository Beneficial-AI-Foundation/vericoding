/-
  Port of vericoding_dafnybench_0606_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RemoveElement (s : Array Int) (k : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem RemoveElement_spec (s : Array Int) (k : Int) (v : Array Int) :=
  (h_0 : 0 ≤ k < s.size)
  : v.size == s.size - 1 ∧ ∀ i :: 0 ≤ i < k → v[i]! == s[i]! ∧ ∀ i :: k ≤ i < v.size → v[i]! == s[i + 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks