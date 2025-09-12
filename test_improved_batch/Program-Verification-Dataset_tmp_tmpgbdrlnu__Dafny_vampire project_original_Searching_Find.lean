/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_vampire project_original_Searching_Find.dfy
  
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