/-
  Port of assertive-programming-assignment-1_tmp_tmp3h_cj44u_SearchAddends_FindAddends.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindAddends (q : seq<int>) (x : Int) : Nat :=
  sorry  -- TODO: implement function body

theorem FindAddends_spec (q : seq<int>) (x : Int) (i : Nat) :=
  (h_0 : Sorted(q) ∧ HasAddends(q, x))
  : i < j < |q| ∧ q[i]!+q[j]! == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks