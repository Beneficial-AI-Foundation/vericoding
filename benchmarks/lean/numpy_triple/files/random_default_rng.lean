-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- BitGenerator represents the underlying random number generator engine -/
structure BitGenerator where
  /-- Internal state of the generator -/
  state : Nat
  /-- Seed used to initialize the generator -/
  seed : Option Nat

/-- Generator provides high-level random number generation methods -/
structure Generator where
  /-- The underlying BitGenerator (PCG64 by default) -/
  bitGenerator : BitGenerator
  /-- Whether the generator has been properly initialized -/
  initialized : Bool
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def default_rng (seed : Option Nat := none) : Id Generator :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem default_rng_spec (seed : Option Nat := none) :
    ⦃⌜True⌝⦄
    default_rng seed
    ⦃⇓result => ⌜result.initialized = true ∧ 
                 result.bitGenerator.seed = seed ∧
                 (seed.isSome → result.bitGenerator.state ≠ 0)⌝⦄ := by
  sorry
-- </vc-theorems>