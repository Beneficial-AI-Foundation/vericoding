import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Evaluate a polynomial specified by its roots at points x.
    If `r` is of length `N`, this function returns the value p(x) = ∏(x - r_i)
    where the product is over all roots r_i in the roots vector. -/
def polyvalfromroots {n m : Nat} (x : Vector Float n) (r : Vector Float m) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => 
    (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, by simp [List.mem_range]⟩)) 1)

-- LLM HELPER
lemma List.mem_of_mem_range {j m : Nat} (h : j ∈ List.range m) : j ∈ List.range m := h

-- LLM HELPER
lemma Nat.lt_of_mem_range {j m : Nat} (h : j ∈ List.range m) : j < m := List.mem_range.mp h

/-- Specification: polyvalfromroots evaluates the polynomial with the given roots
    at each point in x. The polynomial is defined as the product of (x - r_i) for all roots r_i. -/
theorem polyvalfromroots_spec {n m : Nat} (x : Vector Float n) (r : Vector Float m) :
    ⦃⌜True⌝⦄
    polyvalfromroots x r
    ⦃⇓result => ⌜∀ i : Fin n, 
                  result.get i = (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, by simp [List.mem_range]⟩)) 1⌝⦄ := by
  simp only [polyvalfromroots]
  intro i
  simp only [Vector.get_ofFn]
  rfl