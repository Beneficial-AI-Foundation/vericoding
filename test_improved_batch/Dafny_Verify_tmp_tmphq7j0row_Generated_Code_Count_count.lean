/-
  Port of Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Count_count.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def has_count (v : Int) (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def count (v : Int) (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem count_spec (v : Int) (a : Array Int) (n : Int) (r : Int) :=
  (h_0 : n ≥ 0 ∧ n ≤ a.size;)
  : has_count(v, a, n) == r;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks