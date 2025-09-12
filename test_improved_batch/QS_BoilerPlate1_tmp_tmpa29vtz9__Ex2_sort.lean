/-
  Port of QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2_sort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sorted (s : seq<int>) : Bool :=
  sorry  -- TODO: implement function body


  (h_0 : 0 ≤ l ≤ m < r ≤ a.size)
  := by
  sorry  -- TODO: implement proof


  : sorted(a[..])
  := by
  sorry  -- TODO: implement proof


  (h_0 : 0 ≤ l < r ≤ a.size)
  : sorted(a[l..r]) ∧ a[..l] == old(a[..l]) ∧ a[r..] == old(a[r..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks