-- <vc-preamble>
def TestEmulator := Nat × Nat × Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def height (n m : Nat) : Nat :=
sorry

def solve (e : TestEmulator) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem height_nonnegative (n m : Nat) :
  height n m ≥ 0 :=
sorry

theorem height_when_n_geq_m (n m : Nat) :
  n ≥ m → height n m = 2^m - 1 :=
sorry

theorem solve_bounded_by_break_floor (eggs drops break_floor : Nat) :
  eggs > 0 → drops > 0 → break_floor > 0 →
  solve (eggs, drops, break_floor) ≤ break_floor :=
sorry

theorem solve_positive (eggs drops break_floor : Nat) :
  eggs > 0 → drops > 0 → break_floor > 0 →
  solve (eggs, drops, break_floor) > 0 :=
sorry

theorem solve_respects_constraints (eggs drops break_floor : Nat) :
  eggs > 0 → drops > 0 → break_floor > 0 →
  let e := (eggs, drops, break_floor)
  solve e ≤ eggs ∧ solve e ≤ drops :=
sorry

theorem emulator_below_break_point (eggs drops break_floor : Nat) :
  eggs > 0 → drops > 0 → break_floor > 1 →
  solve (eggs, drops - 1, break_floor - 1) = 0 :=
sorry

theorem emulator_at_break_point (eggs drops break_floor : Nat) :
  eggs > 0 → drops > 1 → break_floor > 0 →
  solve (eggs - 1, drops - 2, break_floor) > 0 :=
sorry
-- </vc-theorems>