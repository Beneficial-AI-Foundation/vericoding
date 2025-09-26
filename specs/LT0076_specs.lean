-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tile {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) : Id (Vector α (n * reps)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tile_spec {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) (h_reps : reps > 0) :
    ⦃⌜reps > 0⌝⦄
    tile A reps
    ⦃⇓result => ⌜∀ i : Fin (n * reps), result.get i = A.get ⟨i.val % n, by
      -- We need to prove i.val % n < n
      cases n with
      | zero =>
        -- If n = 0, then n * reps = 0, so there are no valid Fin (n * reps)
        simp at i
        exact absurd i.isLt (Nat.not_lt_zero _)
      | succ n' =>
        -- If n = succ n', then n > 0
        exact Nat.mod_lt i.val (Nat.zero_lt_succ n')
    ⟩⌝⦄ := by
  sorry
-- </vc-theorems>