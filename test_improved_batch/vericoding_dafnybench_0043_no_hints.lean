/-
  Port of vericoding_dafnybench_0043_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindEvenNumbers (arr : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem FindEvenNumbers_spec (arr : Array Int) (evenNumbers : Array Int) :=
  : ∀ x {:trigger (x%2) }:: x in arr[..] ∧  (x%2==0)→ x in evenNumbers[..] ∧ ∀ x :: x !in arr[..] → x !in evenNumbers[..] ∧ ∀ k :: 0 ≤ k < evenNumbers.size → evenNumbers[k]! % 2 == 0 ∧ ∀ k, l :: 0 ≤ k < l < evenNumbers.size →
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks