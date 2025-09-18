-- <vc-preamble>
def number_of_steps (n: Nat) : Nat := sorry

def is_power_of_two (n: Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def simulation_loop (n steps: Nat) : Nat :=
  match n with
  | 0 => steps
  | n+1 => if n % 2 = 0 
           then simulation_loop (n / 2) (steps + 1)
           else simulation_loop (n - 1) (steps + 1)
-- </vc-definitions>

-- <vc-theorems>
theorem number_of_steps_nonneg (n: Nat) : 
  number_of_steps n ≥ 0 := sorry

theorem zero_steps :
  number_of_steps 0 = 0 := sorry
-- </vc-theorems>