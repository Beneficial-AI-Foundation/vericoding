import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Squeeze a single-element vector to extract its value.
    This is a simplified 1D version of numpy.squeeze for vectors of size 1. -/
def squeeze {α : Type} (a : Vector α 1) : Id α :=
  return a.get ⟨0, by decide⟩

-- LLM HELPER
theorem fin_one_unique : ∀ i : Fin 1, i = ⟨0, by decide⟩ := by
  intro i
  cases i with
  | mk val prop =>
    have h : val = 0 := by
      cases val with
      | zero => rfl
      | succ n => 
        simp at prop
        exfalso
        exact Nat.not_succ_le_zero n prop
    simp [h]

/-- Specification: squeeze extracts the single element from a size-1 vector.
    
    Mathematical properties:
    1. The result equals the first (and only) element of the input vector
    2. For any function f, squeeze preserves function application: f(squeeze(a)) = f(a[0])
    3. squeeze is the inverse of creating a single-element vector
    
    Sanity checks:
    - The input must be a vector of exactly size 1
    - The output type changes from Vector to the element type
    - This models numpy's behavior where squeeze([x]) returns x as a 0D array -/
theorem squeeze_spec {α : Type} (a : Vector α 1) :
    ⦃⌜True⌝⦄
    squeeze a
    ⦃⇓result => ⌜result = a.get ⟨0, by decide⟩ ∧ 
                 -- Mathematical property: squeeze is injective
                 (∀ b : Vector α 1, squeeze a = squeeze b → a = b) ∧
                 -- Mathematical property: squeeze preserves function application
                 (∀ (β : Type) (f : α → β), f result = f (a.get ⟨0, by decide⟩)) ∧
                 -- Sanity check: result is the unique element in the vector
                 (∀ i : Fin 1, a.get i = result)⌝⦄ := by
  simp [squeeze]
  apply And.intro
  · rfl
  apply And.intro
  · intro b h
    ext i
    have h1 : a.get ⟨0, by decide⟩ = b.get ⟨0, by decide⟩ := h
    rw [fin_one_unique i]
    exact h1
  apply And.intro
  · intro β f
    rfl
  · intro i
    rw [fin_one_unique i]