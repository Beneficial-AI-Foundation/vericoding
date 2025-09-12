/-
  Port of DafnyProjects_tmp_tmp2acw_s4s_findMax_findMax.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def findMax (a : array<real>) : Float :=
  sorry  -- TODO: implement function body

theorem findMax_spec (a : array<real>) (max : Float) :=
  (h_0 : a.size > 0)
  : ∃ k, 0 ≤ k < a.size ∧ max == a[k]! ∧ ∀ k :: 0 ≤ k < a.size → max ≥ a[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks