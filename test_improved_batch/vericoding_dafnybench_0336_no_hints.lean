/-
  Port of vericoding_dafnybench_0336_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Find (blood : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Find_spec (blood : Array Int) (key : Int) (index : Int) :=
  (h_0 : blood ≠ null)
  : 0 ≤ index → index < blood.size ∧ blood[index]! == key ∧ index < 0 → ∀ k :: 0 ≤ k < blood.size → blood[k]! ≠ key
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks