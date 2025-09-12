/-
  Port of Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search1000.dfy
  
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

end DafnyBenchmarks