-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_inc_dec (n : Int) : Nat :=
  sorry

def xCy (n m : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_inc_dec_non_negative (x : Int) :
  x ≥ 0 → total_inc_dec x ≥ 1 :=
sorry

theorem total_inc_dec_negative (x : Int) :
  x < 0 → total_inc_dec x = 0 :=
sorry

theorem total_inc_dec_monotonic (x : Int) :
  x > 0 → total_inc_dec x > total_inc_dec (x-1) :=
sorry

theorem xCy_non_negative (x y : Int) :
  y ≤ x → xCy x y ≥ 0 :=
sorry

theorem xCy_int_valued (x y : Int) :
  y ≤ x → ∃ n : Int, xCy x y = n :=
sorry

theorem xCy_symmetry (x y : Int) :
  y ≤ x ∧ y > 0 → xCy x y = xCy x (x-y) :=
sorry

theorem xCy_invalid (x y : Int) :
  y > x → xCy x y = 0 :=
sorry
-- </vc-theorems>