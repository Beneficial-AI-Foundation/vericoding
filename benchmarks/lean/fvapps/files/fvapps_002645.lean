-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def faro_cycles (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem faro_cycles_min : faro_cycles 2 = 1 :=
sorry

theorem faro_cycles_positive_small (n : Nat) :
  n = 4 ∨ n = 8 → faro_cycles n > 0 :=
sorry

theorem faro_cycles_standard_deck : faro_cycles 52 = 8 :=
sorry
-- </vc-theorems>