/-
  Port of vericoding_dafnybench_0036_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CanyonSearch (a : Array Int) (b : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem CanyonSearch_spec (a : Array Int) (b : Array Int) (d : Nat) :=
  (h_0 : a.size ≠0 ∧ b.size≠0)
  (h_1 : ∀ i j, 0≤i<j<a.size → a[i]!≤a[j]!)
  (h_2 : ∀ i j, 0≤i<j<b.size → b[i]!≤b[j]!)
  : ∃ i,j:: 0≤i<a.size ∧ 0≤j<b.size ∧ d==if a[i]! < b[j]! then (b[j]!-a[i]!) else (a[i]!-b[j]!) ∧ ∀ i j, 0≤i<a.size ∧ 0≤j<b.size → d≤if a[i]! < b[j]! then (b[j]!-a[i]!) else (a[i]!-b[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks