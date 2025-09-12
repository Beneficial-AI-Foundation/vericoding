/-
  Port of vericoding_dafnybench_0190_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SearchRecursive (a : seq<int>) (i : Int) (j : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SearchRecursive_spec (a : seq<int>) (i : Int) (j : Int) (x : Int) (k : Int) :=
  := by
  sorry  -- TODO: implement proof

def SearchLoop (a : seq<int>) (i : Int) (j : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SearchLoop_spec (a : seq<int>) (i : Int) (j : Int) (x : Int) (k : Int) :=
  (h_0 : 0 ≤ i ≤ j ≤ |a|;)
  : i ≤ k < j ∨ k == -1; ∧ k ≠ -1 → a[k]! == x; ∧ k ≠ -1 → ∀ r | k < r < j :: a[r]! ≠ x; ∧ k == -1 → ∀ r | i ≤ r < j :: a[r]! ≠ x;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks