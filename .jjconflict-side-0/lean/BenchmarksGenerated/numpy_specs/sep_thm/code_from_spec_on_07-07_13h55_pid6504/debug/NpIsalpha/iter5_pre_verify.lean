/-
# NumPy IsAlpha Specification

Port of np_isalpha.dfy to Lean 4
-/

namespace DafnySpecs.NpIsalpha

-- LLM HELPER
def isAlphaChar (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

-- LLM HELPER
def isAlphaString (s : String) : Bool :=
  s.length > 0 ∧ s.all isAlphaChar

/-- Check if strings contain only alphabetic characters -/
def isAlpha {n : Nat} (input : Vector String n) : Vector Bool n :=
  input.map isAlphaString

/-- Specification: The result has same length as input -/
theorem isAlpha_length {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  ret.toList.length = n := by
  simp [isAlpha, Vector.toList_map]

/-- Specification: Alphabetic character check -/
theorem isAlpha_spec {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  ∀ i : Fin n, ret[i] = (input[i].length > 0 ∧
    ∀ j : Nat, j < input[i].length →
      let c := input[i].get ⟨j, by exact Nat.lt_of_lt_of_le j (by assumption) (Nat.le_refl _)⟩
      ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')) := by
  intro i
  simp [isAlpha, Vector.getElem_map, isAlphaString]
  apply Iff.intro
  · intro h
    apply And.intro
    · exact h.1
    · intro j hj
      have : input[i].get ⟨j, hj⟩ ∈ input[i].data := by
        simp [String.get, String.data]
        exact List.get_mem _ _ _
      have char_alpha : isAlphaChar (input[i].get ⟨j, hj⟩) := by
        rw [String.all] at h
        exact h.2 (input[i].get ⟨j, hj⟩) this
      exact char_alpha
  · intro h
    apply And.intro
    · exact h.1
    · rw [String.all]
      intro c hc
      simp [String.data] at hc
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_get.mp hc
      exact h.2 k hk

end DafnySpecs.NpIsalpha