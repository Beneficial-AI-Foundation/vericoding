/-
  Port of Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_SearchLoop.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SearchLoop (a : seq<real>) (i : Int) (j : Int) (x : Float) : Int :=
  sorry  -- TODO: implement function body

theorem SearchLoop_spec (a : seq<real>) (i : Int) (j : Int) (x : Float) (k : Int) :=
  (h_0 : 0 ≤ i ≤ j ≤ |a|;)
  (h_1 : ∀ p, q :: i ≤ p < q < j → a[p]! ≥ a[q]!;)
  : i ≤ k ≤ j; ∧ ∀ r | i ≤ r < k :: a[r]! ≥ x; ∧ ∀ r | k ≤ r < j :: a[r]! < x;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks