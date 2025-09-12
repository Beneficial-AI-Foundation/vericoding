/-
  Port of Clover_below_zero_below_zero.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def below_zero (operations : seq<int>) : Array Int :=
  sorry  -- TODO: implement function body

theorem below_zero_spec (operations : seq<int>) (s : Array Int) :=
  : s.size == |operations| + 1 ∧ s[0]≠=0 ∧ ∀ i :: 0 ≤ i < s.size-1 → s[i+1]==s[i]!+operations[i]! ∧ result == true → (∃ i, 1 ≤ i ≤ |operations| ∧ s[i]! < 0) ∧ result == false → ∀ i :: 0 ≤ i < s.size → s[i]! ≥ 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks