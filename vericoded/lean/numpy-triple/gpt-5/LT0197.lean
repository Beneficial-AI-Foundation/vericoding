import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem get_ofFn' {α : Type _} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simpa using Vector.get_ofFn f i

-- </vc-helpers>

-- <vc-definitions>
def triu {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) : Id (Vector (Vector Float cols) rows) :=
  return Vector.ofFn (fun i : Fin rows =>
  Vector.ofFn (fun j : Fin cols =>
    if h : (i.val : Int) + k ≤ (j.val : Int) then
      (m.get i).get j
    else
      (0 : Float)))
-- </vc-definitions>

-- <vc-theorems>
theorem triu_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    ⦃⌜True⌝⦄
    triu m k
    ⦃⇓result => ⌜
      (∀ i : Fin rows, ∀ j : Fin cols, (i.val : Int) + k ≤ (j.val : Int) → 
        (result.get i).get j = (m.get i).get j) ∧
      (∀ i : Fin rows, ∀ j : Fin cols, (i.val : Int) + k > (j.val : Int) → 
        (result.get i).get j = (0 : Float))⌝⦄ := by
  classical
simpa [triu, get_ofFn'] using
  (by
    intro (_hTrue : True)
    constructor
    · intro i j hij
      have : (i.val : Int) + k ≤ (j.val : Int) := hij
      simp [triu, get_ofFn', this]
    · intro i j hij
      have hle : ¬ (i.val : Int) + k ≤ (j.val : Int) := by
        exact not_le.mpr hij
      simp [triu, get_ofFn', hle])
-- </vc-theorems>
