/-
  Port of QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2_sortAux.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sorted (s : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

def copyArr (a : Array Int) (l : Int) (r : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem copyArr_spec (a : Array Int) (l : Int) (r : Int) (ret : Array Int) :=
  (h_0 : 0 ≤ l < r ≤ a.size)
  : ret[..] == a[l..r]
  := by
  sorry  -- TODO: implement proof


  (h_0 : 0 ≤ l < m < r ≤ a.size)
  (h_1 : sorted(a[l..m]) ∧ sorted(a[m..r]))
  : sorted(a[l..r]) ∧ a[..l] == old(a[..l]) ∧ a[r..] == old(a[r..])
  := by
  sorry  -- TODO: implement proof


  (h_0 : 0 ≤ l < r ≤ a.size)
  : sorted(a[l..r]) ∧ a[..l] == old(a[..l]) ∧ a[r..] == old(a[r..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks