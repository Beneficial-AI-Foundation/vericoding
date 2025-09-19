-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dieSimulator (n: Nat) (rollMax: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dieSimulator_within_bounds (n: Nat) (rollMax: List Nat)
  (h1: 1 ≤ n) (h2: n ≤ 20)
  (h3: rollMax.length = 6)
  (h4: ∀ x ∈ rollMax, 1 ≤ x ∧ x ≤ 15) :
  0 ≤ dieSimulator n rollMax ∧ dieSimulator n rollMax < 1000000007 :=
  sorry

theorem dieSimulator_base_case (rollMax: List Nat)
  (h1: rollMax.length = 6)
  (h2: ∀ x ∈ rollMax, 1 ≤ x ∧ x ≤ 15) :
  dieSimulator 1 rollMax = 6 :=
  sorry

theorem dieSimulator_monotonic (n: Nat) (strict loose: List Nat)
  (h1: strict.length = 6)
  (h2: loose.length = 6)
  (h3: ∀ i ∈ strict, i = 1)
  (h4: ∀ i ∈ loose, i = 15) :
  dieSimulator n strict ≤ dieSimulator n loose :=
  sorry
-- </vc-theorems>