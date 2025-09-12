/-
  Port of vericoding_dafnybench_0197_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Search1000 (a : Array Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search1000_spec (a : Array Int) (x : Int) (k : Int) :=
  (h_0 : a.size ≥ 1000;)
  (h_1 : ∀ p,q | 0 ≤ p < q < 1000 :: a[p]! ≤ a[q]!;)
  : 0 ≤ k ≤ 1000; ∧ ∀ r | 0 ≤ r < k :: a[r]! < x; ∧ ∀ r | k ≤ r < 1000 :: a[r]! ≥ x;
  := by
  sorry  -- TODO: implement proof

def Search2PowLoop (a : Array Int) (i : Int) (n : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search2PowLoop_spec (a : Array Int) (i : Int) (n : Int) (x : Int) (k : Int) :=
  (h_0 : 0 ≤ i ≤ i+n ≤ a.size;)
  (h_1 : ∀ p,q | i ≤ p < q < i+n :: a[p]! ≤ a[q]!;)
  (h_2 : Is2Pow(n+1);)
  : i ≤ k ≤ i+n; ∧ ∀ r | i ≤ r < k :: a[r]! < x; ∧ ∀ r | k ≤ r < i+n :: a[r]! ≥ x;
  := by
  sorry  -- TODO: implement proof

def Search2PowRecursive (a : Array Int) (i : Int) (n : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search2PowRecursive_spec (a : Array Int) (i : Int) (n : Int) (x : Int) (k : Int) :=
  (h_0 : 0 ≤ i ≤ i+n ≤ a.size;)
  (h_1 : ∀ p,q | i ≤ p < q < i+n :: a[p]! ≤ a[q]!;)
  (h_2 : Is2Pow(n+1);)
  : i ≤ k ≤ i+n; ∧ ∀ r | i ≤ r < k :: a[r]! < x; ∧ ∀ r | k ≤ r < i+n :: a[r]! ≥ x;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks