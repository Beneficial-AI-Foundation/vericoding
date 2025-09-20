-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def collatz_steps (n : Nat) (s : String) : Nat :=
  sorry

def get_steps (n : Nat) (len : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem collatz_steps_D : collatz_steps 1 "D" = 2 :=
sorry

theorem collatz_steps_U : collatz_steps 1 "U" = 1 :=
sorry

theorem collatz_steps_geq_input {n : Nat} {s : String} (h : n > 0) :
  collatz_steps n s ≥ n :=
sorry

theorem collatz_steps_minimal {n : Nat} {s : String} (h : n > 0) (h2 : collatz_steps n s > 1) :
  ∀ m, m < collatz_steps n s → ¬(get_steps m (String.length s)).startsWith s :=
sorry

theorem get_steps_matches {n : Nat} {s : String} (h : n > 0) :
  (get_steps (collatz_steps n s) (String.length s)).startsWith s :=
sorry
-- </vc-theorems>