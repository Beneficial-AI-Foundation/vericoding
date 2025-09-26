import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- no helper definitions needed
-- </vc-helpers>

-- <vc-definitions>
def chebadd {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  pure <| Vector.ofFn (fun i : Fin (max n m) =>
  if h1 : i.val < n then
    if h2 : i.val < m then
      c1.get ⟨i.val, h1⟩ + c2.get ⟨i.val, h2⟩
    else
      c1.get ⟨i.val, h1⟩
  else
    if h2 : i.val < m then
      c2.get ⟨i.val, h2⟩
    else
      (0 : Float))
-- </vc-definitions>

-- <vc-theorems>
theorem chebadd_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    chebadd c1 c2
    ⦃⇓result => ⌜(∀ i : Fin (max n m), 
        result.get i = 
          if h1 : i.val < n then
            if h2 : i.val < m then
              c1.get ⟨i.val, h1⟩ + c2.get ⟨i.val, h2⟩
            else
              c1.get ⟨i.val, h1⟩
          else
            if h2 : i.val < m then
              c2.get ⟨i.val, h2⟩
            else
              0) ∧ 
      -- Sanity check: result preserves non-zero coefficients
      (∀ i : Fin n, c1.get i ≠ 0 → ∃ j : Fin (max n m), j.val = i.val ∧ 
        (if h2 : i.val < m then result.get j = c1.get i + c2.get ⟨i.val, h2⟩ else result.get j = c1.get i)) ∧
      (∀ i : Fin m, c2.get i ≠ 0 → ∃ j : Fin (max n m), j.val = i.val ∧ 
        (if h1 : i.val < n then result.get j = c1.get ⟨i.val, h1⟩ + c2.get i else result.get j = c2.get i))
    ⌝⦄ := by
  classical
simpa [chebadd, Vector.get_ofFn] using
  (by
    intro _
    constructor
    · intro i
      simp [chebadd, Vector.get_ofFn]
    · constructor
      · intro i _
        rcases i with ⟨iv, ilt⟩
        let j : Fin (max n m) := ⟨iv, Nat.lt_of_lt_of_le ilt (Nat.le_max_left _ _)⟩
        refine ⟨j, ?_, ?_⟩
        · simp [j]
        · by_cases h2 : iv < m
          · simp [chebadd, Vector.get_ofFn, j, ilt, h2]
          · simp [chebadd, Vector.get_ofFn, j, ilt, h2]
      · intro i _
        rcases i with ⟨iv, ilt⟩
        let j : Fin (max n m) := ⟨iv, Nat.lt_of_lt_of_le ilt (Nat.le_max_right _ _)⟩
        refine ⟨j, ?_, ?_⟩
        · simp [j]
        · by_cases h1 : iv < n
          · simp [chebadd, Vector.get_ofFn, j, ilt, h1]
          · simp [chebadd, Vector.get_ofFn, j, ilt, h1])
-- </vc-theorems>
