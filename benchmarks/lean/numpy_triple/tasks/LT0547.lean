-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seedSequence {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0) 
    (pool_size : Nat := 4) : Id (Vector UInt32 pool_size) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem seedSequence_spec {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    ⦃⌜True⌝⦄
    seedSequence entropy spawn_key pool_size
    ⦃⇓result => ⌜
      -- Reproducibility property: same inputs produce same outputs
      (∀ entropy2 spawn_key2, entropy = entropy2 ∧ spawn_key = spawn_key2 → 
        seedSequence entropy2 spawn_key2 pool_size = result) ∧
      -- Non-degeneracy: output depends on input when entropy is present
      (n > 0 → ∃ i : Fin n, ∃ modified_entropy : Vector UInt32 n,
        modified_entropy ≠ entropy →
        seedSequence modified_entropy spawn_key pool_size ≠ result) ∧
      -- Deterministic: function is well-defined and deterministic
      (∀ call1 call2, call1 = seedSequence entropy spawn_key pool_size ∧
                      call2 = seedSequence entropy spawn_key pool_size → 
                      call1 = call2) ∧
      -- Well-defined output: result has the correct size
      (result.size = pool_size)
    ⌝⦄ := by
  sorry
-- </vc-theorems>