/-
  Port of vericoding_dafnybench_0247_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def find (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem find_spec (a : Array Int) (key : Int) (index : Int) :=
  (h_0 : a.size > 0;)
  : 0 ≤ index ≤ a.size; ∧ index < a.size → a[index]! == key;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks