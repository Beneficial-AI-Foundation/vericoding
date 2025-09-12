/-
  Port of vericoding_dafnybench_0395_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof

def FindAddends (q : seq<int>) (x : Int) : Nat :=
  sorry  -- TODO: implement function body

theorem FindAddends_spec (q : seq<int>) (x : Int) (i : Nat) :=
  (h_0 : Sorted(q) ∧ HasAddends(q, x))
  : i < j < |q| ∧ q[i]!+q[j]! == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks