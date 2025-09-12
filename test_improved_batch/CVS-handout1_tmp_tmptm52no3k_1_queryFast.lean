/-
  Port of CVS-handout1_tmp_tmptm52no3k_1_queryFast.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

def queryFast (a : Array Int) (c : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem queryFast_spec (a : Array Int) (c : Array Int) (i : Int) (j : Int) (r : Int) :=
  (h_0 : a.size + 1 == c.size ∧ c[0]! == 0)
  (h_1 : 0 ≤ i ≤ j ≤ a.size)
  (h_2 : is_prefix_sum_for(a,c))
  : r == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks