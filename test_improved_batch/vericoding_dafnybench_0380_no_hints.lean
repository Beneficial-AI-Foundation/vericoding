/-
  Port of vericoding_dafnybench_0380_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement complex function body

function mem<T(==)> (x: T, l: List<T>) : bool
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
  (h_0 : 0 ≤ i ≤ j ≤ a.size)
  (h_1 : is_prefix_sum_for(a,c))
  : r == sum(a, i, j)
  := by
  sorry  -- TODO: implement proof


  : ∀ i : Int, 0 ≤ i < a.size → mem(a[i]!, l) ∧ ∀ x : T, mem(x, l) → ∃ y: Int :: 0 ≤ y < a.size ∧ a[y]! == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks