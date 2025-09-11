-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 1
-/
-- #guard_msgs in
-- #eval power_mod 11 10 300

/-
info: 5
-/
-- #guard_msgs in
-- #eval power_mod 5 100000000 19

/-
info: 26
-/
-- #guard_msgs in
-- #eval power_mod 9 193125 37
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded