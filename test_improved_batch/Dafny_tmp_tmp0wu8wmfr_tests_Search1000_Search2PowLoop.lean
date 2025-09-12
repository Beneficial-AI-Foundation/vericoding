/-
  Port of Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search2PowLoop.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Search2PowLoop (a : Array Int) (i : Int) (n : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search2PowLoop_spec (a : Array Int) (i : Int) (n : Int) (x : Int) (k : Int) :=
  (h_0 : 0 ≤ i ≤ i+n ≤ a.size;)
  (h_1 : ∀ p,q | i ≤ p < q < i+n :: a[p]! ≤ a[q]!;)
  (h_2 : Is2Pow(n+1);)
  : i ≤ k ≤ i+n; ∧ ∀ r | i ≤ r < k :: a[r]! < x; ∧ ∀ r | k ≤ r < i+n :: a[r]! ≥ x;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks