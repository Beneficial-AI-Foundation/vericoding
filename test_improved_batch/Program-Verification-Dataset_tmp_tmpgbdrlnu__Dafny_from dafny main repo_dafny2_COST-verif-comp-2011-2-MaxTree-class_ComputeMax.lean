/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-2-MaxTree-class_ComputeMax.dfy
  
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