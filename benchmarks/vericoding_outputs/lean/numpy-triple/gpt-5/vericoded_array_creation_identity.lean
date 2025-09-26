import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem Vector.get_ofFn' {α : Type _} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simpa using Vector.get_ofFn f i
-- </vc-helpers>

-- <vc-definitions>
def identity (n : Nat) : Id (Vector (Vector Float n) n) :=
  pure <| Vector.ofFn (fun i => Vector.ofFn (fun j => if i = j then (1.0 : Float) else (0.0 : Float)))
-- </vc-definitions>

-- <vc-theorems>
theorem identity_spec (n : Nat) :
    ⦃⌜True⌝⦄
    identity n
    ⦃⇓result => ⌜∀ i j : Fin n, 
                   (result.get i).get j = if i = j then (1.0 : Float) else (0.0 : Float)⌝⦄ := by
  simpa [identity] using
  (by
    intro (_ : True)
    intro i j
    simp [Vector.get_ofFn'])
-- </vc-theorems>
