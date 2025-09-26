import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Index into `values` cyclically using the position `i` and the proof that `m > 0`. -/
def cycleIdx {n m : Nat} (i : Fin n) (h : m > 0) : Fin m :=
  ⟨i.val % m, Nat.mod_lt i.val h⟩

-- LLM HELPER
@[simp] theorem get_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  classical
  cases i with
  | mk idx isLt =>
    simpa [Vector.get, Vector.ofFn]
-- </vc-helpers>

-- <vc-definitions>
def putmask {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) : Id (Vector Float n) :=
  return Vector.ofFn (fun i => if mask.get i then values.get (cycleIdx (n:=n) (m:=m) i h) else a.get i)
-- </vc-definitions>

-- <vc-theorems>
theorem putmask_spec {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) :
    ⦃⌜m > 0⌝⦄
    putmask a mask values h
    ⦃⇓result => ⌜(∀ i : Fin n, mask.get i = true → result.get i = values.get ⟨i.val % m, Nat.mod_lt i.val h⟩) ∧
                (∀ i : Fin n, mask.get i = false → result.get i = a.get i) ∧
                (∀ i : Fin n, mask.get i = true → ∃ j : Fin m, result.get i = values.get j)⌝⦄ := by
  classical
intro _hpre
constructor
· intro i htrue
  simp [putmask, get_ofFn, htrue, cycleIdx]
· constructor
  · intro i hfalse
    simp [putmask, get_ofFn, hfalse, cycleIdx]
  · intro i htrue
    refine ⟨⟨i.val % m, Nat.mod_lt i.val h⟩, ?_⟩
    simp [putmask, get_ofFn, htrue, cycleIdx]
-- </vc-theorems>
