-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000003

def calculate_particles (n: Nat) (x: Nat) : Nat :=
  sorry

theorem result_bounds (n x : Nat) : 
  calculate_particles n x < MOD := by
  sorry

theorem large_n_is_zero (n x : Nat) : 
  n ≥ MOD → calculate_particles n x = 0 := by
  sorry

theorem zero_case (x : Nat) :
  calculate_particles 0 x = x % MOD := by
  sorry

theorem one_case (x : Nat) :
  calculate_particles 1 x = x % MOD := by
  sorry

theorem factorial_case (n : Nat) :
  calculate_particles n 1 = (List.range n).foldl (fun acc i => (acc * (i + 1)) % MOD) 1 := by
  sorry

theorem multiplication_property (n x : Nat) :
  calculate_particles n x = (calculate_particles n 1 * x) % MOD := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_particles 1 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_particles 2 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_particles 3 1

-- Apps difficulty: interview
-- Assurance level: guarded