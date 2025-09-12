/-
  Port of vericoding_dafnybench_0386_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (a : Array Int) (max : Int) :=
  (h_0 : a ≠ null;)
  : ∀ j :: j ≥ 0 ∧ j < a.size → max ≥ a[j]!; //max is larger then anything in the array ∧ a.size > 0 → ∃ j, j ≥ 0 ∧ j < a.size ∧ max == a[j]!; //max is an element in the array
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks