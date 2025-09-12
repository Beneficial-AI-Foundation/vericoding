/-
  Port of vericoding_dafnybench_0165_ground_truth.dfy
  
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