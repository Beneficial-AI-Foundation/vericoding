/-
  Port of Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout1_queryFast.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (a : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

function mem<T(==)> (x: T, l: List<T>) : bool
  sorry  -- TODO: implement complex function body

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