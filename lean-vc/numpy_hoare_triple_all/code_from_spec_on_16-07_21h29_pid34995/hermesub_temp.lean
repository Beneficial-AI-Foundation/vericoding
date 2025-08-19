import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.mk' (l : List α) : Vector α l.length :=
  ⟨l.toArray, by simp⟩

-- LLM HELPER
def Vector.get_mk' (l : List α) (i : Fin l.length) : (Vector.mk' l).get i = l.get i := by
  simp [Vector.mk', Vector.get, List.getElem_toArray]

/-- Subtract one Hermite series from another.
    Returns the difference of two Hermite series c1 - c2.
    The sequences of coefficients are from lowest order term to highest. -/
def hermesub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  pure $ ⟨(List.ofFn (fun i : Fin (max n m) => 
    (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else 0) - 
    (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else 0))).toArray, by simp⟩

/-- Specification: hermesub performs component-wise subtraction of Hermite series coefficients.
    The result has length equal to the maximum of the input lengths, with shorter arrays
    implicitly padded with zeros. This captures the mathematical property that polynomial 
    subtraction is component-wise and preserves the polynomial structure. -/
theorem hermesub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermesub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
      result.get i = (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else 0) - 
                     (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else 0)⌝⦄ := by
  unfold hermesub
  simp only [Triple.pure]
  intro i
  simp [Vector.get, List.getElem_toArray, List.getElem_ofFn]