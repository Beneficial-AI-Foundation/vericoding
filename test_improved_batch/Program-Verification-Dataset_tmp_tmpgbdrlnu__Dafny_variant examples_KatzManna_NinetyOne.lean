/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_variant examples_KatzManna_NinetyOne.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NinetyOne (x : Int) (ghost proveFunctionalPostcondition : Bool) : Int :=
  sorry  -- TODO: implement function body

theorem NinetyOne_spec (x : Int) (ghost proveFunctionalPostcondition : Bool) (z : Int) :=
  : proveFunctionalPostcondition → z == if x > 101 then x-10 else 91;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks