/-
  Port of formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex1_PalVerify.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def PalVerify (a : Array Char) : Bool :=
  sorry  -- TODO: implement function body

theorem PalVerify_spec (a : Array Char) (yn : Bool) :=
  : yn == true → ∀ i :: 0 ≤ i < a.size/2 → a[i]! == a[a.size - i -1] ∧ yn == false → ∃ i, 0 ≤ i < a.size/2 ∧ a[i]! ≠ a[a.size - i -1] ∧ ∀ j :: 0≤j<a.size → a[j]! == old(a[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks