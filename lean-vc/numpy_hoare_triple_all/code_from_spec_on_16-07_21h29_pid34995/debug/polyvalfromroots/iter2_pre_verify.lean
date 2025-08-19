import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Evaluate a polynomial specified by its roots at points x.
    If `r` is of length `N`, this function returns the value p(x) = ∏(x - r_i)
    where the product is over all roots r_i in the roots vector. -/
def polyvalfromroots {n m : Nat} (x : Vector Float n) (r : Vector Float m) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn fun i => 
    (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, List.mem_range.mp (List.mem_of_mem_range j)⟩)) 1)

-- LLM HELPER
lemma range_mem_bound (j : Nat) (m : Nat) (h : j ∈ List.range m) : j < m := by
  exact List.mem_range.mp h

-- LLM HELPER
lemma List.mem_of_mem_range (j : Nat) : j ∈ List.range m → j < m := by
  exact List.mem_range.mp

/-- Specification: polyvalfromroots evaluates the polynomial with the given roots
    at each point in x. The polynomial is defined as the product of (x - r_i) for all roots r_i. -/
theorem polyvalfromroots_spec {n m : Nat} (x : Vector Float n) (r : Vector Float m) :
    ⦃⌜True⌝⦄
    polyvalfromroots x r
    ⦃⇓result => ⌜∀ i : Fin n, 
                  result.get i = (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, range_mem_bound j m (List.mem_of_mem_range j)⟩)) 1⌝⦄ := by
  simp [polyvalfromroots]
  intro i
  simp [Vector.get, Vector.ofFn]
  rfl