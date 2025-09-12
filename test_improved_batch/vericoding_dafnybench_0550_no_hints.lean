/-
  Port of vericoding_dafnybench_0550_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Min (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Min_spec (a : Int) (b : Int) (minValue : Int) :=
  : minValue == a ∨ minValue == b ∧ minValue ≤ a ∧ minValue ≤ b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks