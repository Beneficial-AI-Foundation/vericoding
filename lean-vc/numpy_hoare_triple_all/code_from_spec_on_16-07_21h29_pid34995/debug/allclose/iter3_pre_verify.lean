import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.allclose: Returns True if two arrays are element-wise equal within a tolerance.

    The tolerance values are positive, typically very small numbers. The
    relative difference (rtol * abs(b)) and the absolute difference
    atol are added together to compare against the absolute difference
    between a and b.

    For each element, the condition is:
    absolute(a - b) <= (atol + rtol * absolute(b))

    This function returns True if ALL elements satisfy this condition,
    False otherwise.
-/
def allclose {n : Nat} (a b : Vector Float n) (rtol atol : Float) : Id Bool := do
  let mut result := true
  for i in List.range n do
    let idx : Fin n := ⟨i, by simp [List.mem_range]⟩
    if ¬(Float.abs (a.get idx - b.get idx) <= atol + rtol * Float.abs (b.get idx)) then
      result := false
      break
  return result

-- LLM HELPER
lemma allclose_unfold {n : Nat} (a b : Vector Float n) (rtol atol : Float) :
    allclose a b rtol atol = do
      let mut result := true
      for i in List.range n do
        let idx : Fin n := ⟨i, by simp [List.mem_range]⟩
        if ¬(Float.abs (a.get idx - b.get idx) <= atol + rtol * Float.abs (b.get idx)) then
          result := false
          break
      return result := by
  rfl

/-- Specification: allclose returns true iff all elements are within tolerance.

    Precondition: rtol >= 0 and atol >= 0 (tolerance values must be non-negative)
    Postcondition: result = true iff all elements satisfy the tolerance condition
                   abs(a[i] - b[i]) <= atol + rtol * abs(b[i]) for all i
-/
theorem allclose_spec {n : Nat} (a b : Vector Float n) (rtol atol : Float) 
    (h_rtol : rtol >= 0) (h_atol : atol >= 0) :
    ⦃⌜rtol >= 0 ∧ atol >= 0⌝⦄
    allclose a b rtol atol
    ⦃⇓result => ⌜result = (∀ i : Fin n, Float.abs (a.get i - b.get i) <= atol + rtol * Float.abs (b.get i))⌝⦄ := by
  intro h
  unfold allclose
  apply pure_spec
  rfl