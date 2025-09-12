/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_VSComp2010_Problem1-SumMax_M.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def M (N : Int) (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem M_spec (N : Int) (a : Array Int) (sum : Int) :=
  (h_0 : 0 ≤ N ∧ a.size == N ∧ (∀ k :: 0 ≤ k ∧ k < N → 0 ≤ a[k]!);)
  : sum ≤ N * max;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks