/-
  Port of vericoding_dafnybench_0362_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def firste (a : Array Char) : Int :=
  sorry  -- TODO: implement function body

theorem firste_spec (a : Array Char) (c : Int) :=
  : -1 ≤ c < a.size ∧ 0 ≤ c < a.size → a[c]! == 'e' ∧ ∀ x :: 0 ≤ x < c → a[x]! ≠ 'e' ∧ c == -1 → ∀ x :: 0 ≤ x < a.size → a[x]! ≠ 'e'
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks