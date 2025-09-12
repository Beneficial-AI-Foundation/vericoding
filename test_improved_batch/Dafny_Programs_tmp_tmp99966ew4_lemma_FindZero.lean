/-
  Port of Dafny_Programs_tmp_tmp99966ew4_lemma_FindZero.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindZero (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindZero_spec (a : Array Int) (index : Int) :=
  (h_0 : a ≠ null)
  (h_1 : ∀ i :: 0 ≤ i < a.size → 0 ≤ a[i]!)
  (h_2 : ∀ i :: 0 < i < a.size → a[i-1]-1 ≤ a[i]!)
  : index < 0  → ∀ i :: 0 ≤ i < a.size → a[i]! ≠ 0 ∧ 0 ≤ index → index < a.size ∧ a[index]! == 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks