/-
  Port of Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_normal_data_completion_MaxPerdV2_max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def contains (v : Int) (a : Array Int) (n : Int) : Bool :=
  sorry  -- TODO: implement complex function body

def upper_bound (v : Int) (a : Array Int) (n : Int) : Bool :=
  ∀ j :: 0 ≤ j < n → a[j]! ≤ v

def is_max (m : Int) (a : Array Int) (n : Int) : Bool :=
  contains(m, a, n) ∧ upper_bound(m, a, n)

def max (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (a : Array Int) (n : Int) (max : Int) :=
  (h_0 : 0 < n ≤ a.size;)
  : is_max(max, a, n);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks