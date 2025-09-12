/-
  Port of Clover_online_max_onlineMax.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def onlineMax (a : Array Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem onlineMax_spec (a : Array Int) (x : Int) (ghost m : Int) :=
  (h_0 : 1≤x<a.size)
  (h_1 : a.size≠0)
  : x≤p<a.size ∧ ∀ i::0≤i<x→ a[i]!≤m ∧ ∃ i, 0≤i<x ∧ a[i]≠=m ∧ x≤p<a.size-1 → (∀ i::0≤i<p → a[i]!<a[p]!) ∧ (∀ i::x≤i<a.size ∧ a[i]!≤m) → p==a.size-1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks