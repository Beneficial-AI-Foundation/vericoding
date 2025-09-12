/-
  Port of vericoding_dafnybench_0019_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

function mem<T(==)> (x: T, l:List<T>) : bool
  sorry  -- TODO: implement function body

def query (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem query_spec (a : Array Int) (i : Int) (j : Int) (s : Int) :=
  (h_0 : 0 ≤ i ≤ j ≤ a.size)
  : s == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof

def queryFast (a : Array Int) (c : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

theorem queryFast_spec (a : Array Int) (c : Array Int) (i : Int) (j : Int) (r : Int) :=
  (h_0 : is_prefix_sum_for(a,c) ∧ 0 ≤ i ≤ j ≤ a.size < c.size)
  : r == sum(a, i,j)
  := by
  sorry  -- TODO: implement proof


  (h_0 : a.size > 0)
  : ∀ j::0 ≤ j < a.size → mem(a[j]!,l)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks