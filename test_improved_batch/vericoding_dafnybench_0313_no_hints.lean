/-
  Port of vericoding_dafnybench_0313_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsEmpty  : Bool :=
  sorry  -- TODO: implement complex function body

def ComputeMax  : Int :=
  sorry  -- TODO: implement function body

theorem ComputeMax_spec (mx : Int) :=
  (h_0 : Valid() ∧ !IsEmpty();)
  : ∀ x :: x in Contents → x ≤ mx; ∧ ∃ x, x in Contents ∧ x == mx;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks