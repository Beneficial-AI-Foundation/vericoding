/-
  Port of Dafny_tmp_tmpv_d3qi10_2_min_minMethod.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (a : Int) (b : Int) : Int :=
  if a < b then a else b

def minMethod (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem minMethod_spec (a : Int) (b : Int) (c : Int) :=
  : c ≤ a ∧ c ≤ b ∧ c == a ∨ c == b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks