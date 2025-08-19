import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Multiply a polynomial by x.
    Multiplies polynomial c by x, where x is the independent variable.
    For polynomial p(x) = c[0] + c[1]*x + ... + c[n-1]*x^(n-1),
    returns x*p(x) = 0 + c[0]*x + c[1]*x^2 + ... + c[n-1]*x^n -/
def polymulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) := do
  let result_data := 0 :: c.toList
  return ⟨result_data.toArray, by simp [List.length_cons, Vector.length_toList]⟩

-- LLM HELPER
lemma vector_get_zero {n : Nat} (c : Vector Float n) : 
    let result := ⟨(0 :: c.toList).toArray, by simp [List.length_cons, Vector.length_toList] : Vector Float (n + 1)⟩
    result.get ⟨0, by simp⟩ = 0 := by
  simp [Vector.get_eq_getElem, Vector.getElem_eq_getElem_toArray]

-- LLM HELPER
lemma vector_get_succ {n : Nat} (c : Vector Float n) (i : Fin n) :
    let result := ⟨(0 :: c.toList).toArray, by simp [List.length_cons, Vector.length_toList] : Vector Float (n + 1)⟩
    result.get ⟨i.val + 1, by simp⟩ = c.get i := by
  simp [Vector.get_eq_getElem, Vector.getElem_eq_getElem_toArray]
  rw [List.getElem_toArray]
  rw [List.getElem_cons_succ]
  rw [← List.getElem_toArray]
  rw [← Vector.getElem_eq_getElem_toArray]
  rw [← Vector.get_eq_getElem]

/-- Specification: polymulx multiplies a polynomial by x.
    The result has one more coefficient than the input.
    The first coefficient is always 0, and subsequent coefficients
    are the original coefficients shifted by one position.
    This represents multiplying p(x) by x to get x*p(x). -/
theorem polymulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    polymulx c
    ⦃⇓result => ⌜result.get ⟨0, by simp⟩ = 0 ∧ 
                 ∀ i : Fin n, result.get ⟨i.val + 1, by simp⟩ = c.get i⌝⦄ := by
  simp [polymulx]
  apply and_intro
  · apply vector_get_zero
  · intro i
    apply vector_get_succ