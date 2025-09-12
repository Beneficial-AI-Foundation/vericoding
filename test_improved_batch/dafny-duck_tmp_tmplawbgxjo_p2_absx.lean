/-
  Port of dafny-duck_tmp_tmplawbgxjo_p2_absx.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Nat :=
  sorry  -- TODO: implement function body

def absx (x : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem absx_spec (x : Array Int) (y : Array Int) :=
  : y.size == x.size ∧ ∀ i :: 0 ≤ i < y.size →  y[i]! == abs(x[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks