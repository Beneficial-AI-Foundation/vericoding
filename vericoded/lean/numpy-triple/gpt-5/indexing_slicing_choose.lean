import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No extra helpers needed; rely on standard simp lemmas like Vector.get_ofFn.
-- </vc-helpers>

-- <vc-definitions>
def choose {n num_choices : Nat} (indices : Vector (Fin num_choices) n) 
          (choices : Vector (Vector Float n) num_choices) : Id (Vector Float n) :=
  pure <| Vector.ofFn (fun i : Fin n => (choices.get (indices.get i)).get i)
-- </vc-definitions>

-- <vc-theorems>
theorem choose_spec {n num_choices : Nat} (indices : Vector (Fin num_choices) n) 
                   (choices : Vector (Vector Float n) num_choices) :
    ⦃⌜True⌝⦄
    choose indices choices
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (choices.get (indices.get i)).get i⌝⦄ := by
  simpa [choose] using
    (by
      intro (_ : True)
      intro i
      simp
    )
-- </vc-theorems>
