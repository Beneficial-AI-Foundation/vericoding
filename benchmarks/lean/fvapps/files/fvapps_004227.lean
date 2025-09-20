-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def WEEKDAY : Nat → String :=
sorry

def ERROR : String :=
sorry

def whatday (n : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem whatday_spec (n : Int) :
  (1 ≤ n ∧ n ≤ 7 → ∃ (i : Nat), whatday n = WEEKDAY i) ∧
  (¬(1 ≤ n ∧ n ≤ 7) → whatday n = ERROR) :=
sorry

theorem valid_weekday (n : Int) (h : 1 ≤ n ∧ n ≤ 7) :
  ∃ (i : Nat), whatday n = WEEKDAY i :=
sorry

theorem invalid_weekday (n : Int) (h : ¬(1 ≤ n ∧ n ≤ 7)) :
  whatday n = ERROR :=
sorry
-- </vc-theorems>