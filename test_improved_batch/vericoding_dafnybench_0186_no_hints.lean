/-
  Port of vericoding_dafnybench_0186_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def add_small_numbers (a : Array Int) (n : Int) (max : Int) : Int :=
  sorry  -- TODO: implement function body

theorem add_small_numbers_spec (a : Array Int) (n : Int) (max : Int) (r : Int) :=
  (h_0 : n > 0;)
  (h_1 : n ≤ a.size;)
  (h_2 : (∀ i : Int, 0 ≤ i ∧ i < n → a[i]! ≤ max);)
  : r ≤ max * n;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks