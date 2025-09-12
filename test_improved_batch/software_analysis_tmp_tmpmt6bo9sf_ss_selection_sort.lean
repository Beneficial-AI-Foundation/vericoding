/-
  Port of software_analysis_tmp_tmpmt6bo9sf_ss_selection_sort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def find_min_index (a : Array Int) (s : Int) (e : Int) : Int :=
  sorry  -- TODO: implement function body

theorem find_min_index_spec (a : Array Int) (s : Int) (e : Int) (min_i : Int) :=
  (h_0 : a.size > 0)
  (h_1 : 0 ≤ s < a.size)
  (h_2 : e ≤ a.size)
  (h_3 : e > s)
  := by
  sorry  -- TODO: implement proof


  (h_0 : ns.size ≥ 0)
  : is_sorted(ns[..]) ∧ is_permutation2(old(ns[..]), ns[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks