-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerMod (b e m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powermod_range (b e m : Nat) (h : m ≥ 2) :
  let r := powerMod b e m
  0 ≤ r ∧ r < m :=
  sorry

theorem powermod_zero_exp (base m : Nat) (h : base ≥ 1) (h' : m ≥ 2) :
  powerMod base 0 m = 1 :=
  sorry

theorem powermod_identity (b m : Nat) (h : b ≥ 1) (h' : m ≥ 2) :
  powerMod b 1 m = b % m :=
  sorry

theorem powermod_multiplicative (b e m : Nat) 
  (h1 : b ≥ 1) (h2 : e ≥ 1) (h3 : m ≥ 2) :
  (powerMod b e m * powerMod b (e + 1) m) % m = powerMod b (e + e + 1) m :=
  sorry
-- </vc-theorems>