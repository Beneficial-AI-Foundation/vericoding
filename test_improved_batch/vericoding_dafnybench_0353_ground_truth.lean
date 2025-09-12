/-
  Port of vericoding_dafnybench_0353_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def StringSwap (s : String) (i : Nat) (j : Nat) : String :=
  sorry  -- TODO: implement function body

theorem StringSwap_spec (s : String) (i : Nat) (j : Nat) (t : String) :=
  (h_0 : i ≥ 0 ∧ j ≥ 0 ∧ |s| ≥ 0;)
  (h_1 : |s| > 0 → i < |s| ∧ j < |s|;)
  : multiset(s[..]) == multiset(t[..]); ∧ |s| == |t|; ∧ |s| > 0 → ∀ k : nat, k ≠ i ∧ k ≠ j ∧ k < |s| → t[k]! == s[k]! ∧ |s| > 0 → t[i]! == s[j]! ∧ t[j]! == s[i]!; ∧ |s| == 0 → t == s;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks