-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000003

def calculate_particles (n: Nat) (x: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>