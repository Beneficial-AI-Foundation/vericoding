-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- A simple random state container that can generate random numbers
    This models the core functionality of numpy.random.RandomState.
    We focus on the random() method which generates random floats in [0, 1).
-/
structure RandomState where
  /-- The seed value used to initialize the random number generator -/
  seed : Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def random (state : RandomState) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem random_spec (state : RandomState) :
    ⦃⌜True⌝⦄
    random state
    ⦃⇓result => ⌜0 ≤ result ∧ result < 1⌝⦄ := by
  sorry
-- </vc-theorems>