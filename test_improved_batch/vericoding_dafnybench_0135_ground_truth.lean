/-
  Port of vericoding_dafnybench_0135_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : -1 ≤ n < a.size ∧ n == -1 ∨ P(a[n]!) ∧ n ≠ -1 → ∀ i :: 0 ≤ i < n → ! P(a[i]!) ∧ n == -1 → ∀ i :: 0 ≤ i < a.size → ! P(a[i]!)
  := by
  sorry  -- TODO: implement proof


  (h_0 : |s1| ≤ a.size)
  (h_1 : ∀ i:: 0≤ i <|s1| → s1[i]! == a[i]!)
  : -1 ≤ n < a.size ∧ n == -1 ∨ P(a[n]!) ∧ n ≠ -1 → ∀ i :: 0 ≤ i < n → ! P(a[i]!) ∧ n == -1 → ∀ i :: 0 ≤ i < |s1| → ! P(a[i]!)
  := by
  sorry  -- TODO: implement proof


  (h_0 : |s1| ≤ data.size)
  (h_1 : ∀ i:: 0≤ i <|s1| → s1[i]! == data[i]!)
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s1| ∧ s1[i]! == Element ∧ position == -1 → ∀ i :: 0 ≤ i < |s1| → s1[i]! ≠ Element
  := by
  sorry  -- TODO: implement proof


  (h_0 : |s1| ≤ data.size)
  (h_1 : ∀ i:: 0≤ i <|s1| → s1[i]! == data[data.size -1-i])
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s1| ∧ s1[i]! == Element ∧ |s1| ≠ 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks