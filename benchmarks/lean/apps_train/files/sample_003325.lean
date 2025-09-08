/-
Your task is to create a new implementation of `modpow` so that it computes `(x^y)%n` for large `y`. The problem with the current implementation is that the output of `Math.pow` is so large on our inputs that it won't fit in a 64-bit float.

You're also going to need to be efficient, because we'll be testing some pretty big numbers.
-/

-- <vc-helpers>
-- </vc-helpers>

def powerMod (b e m : Nat) : Nat :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded