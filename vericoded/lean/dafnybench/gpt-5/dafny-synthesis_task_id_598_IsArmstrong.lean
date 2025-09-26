import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: enable classical logic for deciding propositions
noncomputable section
open Classical

-- LLM HELPER: coerce Prop to Bool via decide
instance instCoePropBool : Coe Prop Bool where
  coe := fun p => decide p
-- </vc-helpers>

-- <vc-definitions>
def IsArmstrong (n : Int) : Bool :=
(n = ((n / 100) * (n / 100) * (n / 100) +
      ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
      (n % 10) * (n % 10) * (n % 10)))
-- </vc-definitions>

-- <vc-theorems>
theorem IsArmstrong_spec (n : Int) :
100 ≤ n ∧ n < 1000 →
IsArmstrong n = (n = ((n / 100) * (n / 100) * (n / 100) +
((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
(n % 10) * (n % 10) * (n % 10))) :=
by
  intro _
  rfl
-- </vc-theorems>
