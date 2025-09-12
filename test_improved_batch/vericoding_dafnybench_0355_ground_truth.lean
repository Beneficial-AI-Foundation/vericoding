/-
  Port of vericoding_dafnybench_0355_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BadSort (a : String) : String :=
  sorry  -- TODO: implement function body

theorem BadSort_spec (a : String) (b : String) :=
  (h_0 : ∀ k :: 0 ≤ k < |a| → a[k]! == 'b' ∨ a[k]! == 'a' ∨ a[k]! == 'd';)
  : sortedbad(b); ∧ multiset(a[..]) == multiset(b[..]); ∧ |a| == |b|;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks