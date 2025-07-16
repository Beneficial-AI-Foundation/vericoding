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
  simp [isAlpha]
  rw [Vector.toList_map]
  simp [Vector.toList_length]

/-- Specification: Alphabetic character check -/
theorem isAlpha_spec {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  ∀ i : Fin n, ret[i] = (input[i].length > 0 ∧
    ∀ j : Nat, j < input[i].length →
      let c := input[i].get ⟨j, by assumption⟩
      ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')) := by
  intro i
  simp [isAlpha, Vector.map_get]
  simp [isAlphaString]
  constructor
  · intro h
    constructor
    · exact h.1
    · intro j hj
      simp [isAlphaChar] at h
      exact h.2 (input[i].get ⟨j, hj⟩)
  · intro h
    constructor
    · exact h.1
    · simp [String.all, isAlphaChar]
      intro c hc
      exact h.2 c.val c.property

end DafnySpecs.NpIsalpha