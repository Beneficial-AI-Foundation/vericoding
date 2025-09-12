/-
  Port of CVS-handout1_tmp_tmptm52no3k_1_query.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

def query (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem query_spec (a : Array Int) (i : Int) (j : Int) (res : Int) :=
  (h_0 : 0 ≤ i ≤ j ≤ a.size)
  : res == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks