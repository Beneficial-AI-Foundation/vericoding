-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_mia_save_300 (days: Nat) (min_wage: Nat) (highest_tip: Nat) (shifts: List Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem earnings_increase_with_min_wage 
  (days: Nat) (min_wage: Nat) (highest_tip: Nat) (shifts: List Nat)
  (h1: days > 0) (h2: min_wage > 0) :
  can_mia_save_300 days (min_wage + 1) highest_tip (shifts.take days) ≥ 
  can_mia_save_300 days min_wage highest_tip (shifts.take days) := 
  sorry

theorem earnings_increase_with_tips
  (days: Nat) (min_wage: Nat) (highest_tip: Nat) (shifts: List Nat)
  (h1: days > 0) (h2: highest_tip > 0) :
  can_mia_save_300 days min_wage (highest_tip + 1) (shifts.take days) ≥
  can_mia_save_300 days min_wage highest_tip (shifts.take days) :=
  sorry

theorem earnings_increase_with_days
  (days: Nat) (min_wage: Nat) (highest_tip: Nat) (shifts: List Nat)
  (h1: days > 0) (h2: shifts.length > days) :
  can_mia_save_300 (days + 1) min_wage highest_tip (shifts.take (days + 1)) ≥
  can_mia_save_300 days min_wage highest_tip (shifts.take days) :=
  sorry
-- </vc-theorems>