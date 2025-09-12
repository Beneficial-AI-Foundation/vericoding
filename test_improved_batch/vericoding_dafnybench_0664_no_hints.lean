/-
  Port of vericoding_dafnybench_0664_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  (h_0 : x == -1)
  : 0 ≤ y ∧ 0 ≤ x → y == x ∧ x < 0 → y == -x
  := by
  sorry  -- TODO: implement proof

def Abs2 (x : Float) : Float :=
  sorry  -- TODO: implement function body

theorem Abs2_spec (x : Float) (y : Float) :=
  (h_0 : x == -0.5)
  : 0.0 ≤ y ∧ 0.0 ≤ x → y == x ∧ x < 0.0 → y == -x
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks