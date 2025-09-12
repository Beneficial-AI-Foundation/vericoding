/-
  Port of Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 1_Lab3_ComputeFact.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def factorial (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def sumSerie (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def ComputeFact (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem ComputeFact_spec (n : Int) (f : Int) :=
  (h_0 : n ≥0)
  : f== factorial(n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks