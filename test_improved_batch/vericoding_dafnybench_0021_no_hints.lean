/-
  Port of vericoding_dafnybench_0021_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement complex function body

def query (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem query_spec (a : Array Int) (i : Int) (j : Int) (res : Int) :=
  (h_0 : 0 ≤ i ≤ j ≤ a.size)
  : res == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof

def queryFast (a : Array Int) (c : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem queryFast_spec (a : Array Int) (c : Array Int) (i : Int) (j : Int) (r : Int) :=
  (h_0 : a.size + 1 == c.size ∧ c[0]! == 0)
  (h_1 : 0 ≤ i ≤ j ≤ a.size)
  (h_2 : is_prefix_sum_for(a,c))
  : r == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks