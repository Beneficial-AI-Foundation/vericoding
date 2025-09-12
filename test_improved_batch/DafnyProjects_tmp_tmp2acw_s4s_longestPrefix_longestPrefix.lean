/-
  Port of DafnyProjects_tmp_tmp2acw_s4s_longestPrefix_longestPrefix.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def longestPrefix (a : Array Int) (b : array <int>) : Nat :=
  sorry  -- TODO: implement function body

theorem longestPrefix_spec (a : Array Int) (b : array <int>) (i : Nat) :=
  : i ≤ a.size ∧ i ≤ b.size ∧ a[..i] == b[..i] ∧ i < a.size ∧ i < b.size → a[i]! ≠ b[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks