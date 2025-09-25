-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DrinkType := Char

def calculate_milk_tea_cost (sequence : List DrinkType) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem milk_tea_cost_non_negative (sequence : List DrinkType) :
  calculate_milk_tea_cost sequence ≥ 0 :=
sorry

theorem milk_tea_cost_upper_bound (sequence : List DrinkType) :
  calculate_milk_tea_cost sequence ≤ sequence.length * 4 :=
sorry

theorem milk_tea_cost_lower_bound (sequence : List DrinkType) :
  let stamp_redemptions := sequence.length / 6
  calculate_milk_tea_cost sequence ≥ max 0 (sequence.length * 3 - stamp_redemptions * 3) :=
sorry

theorem sixth_drink_reduces_cost (sequence : List DrinkType) (d : DrinkType) :
  sequence.length = 6 →
  calculate_milk_tea_cost sequence ≥ calculate_milk_tea_cost (sequence ++ [d]) :=
sorry

theorem seventh_drink_free (sequence : List DrinkType) :
  sequence.length = 7 →
  calculate_milk_tea_cost (sequence.take 6) = calculate_milk_tea_cost sequence :=
sorry

theorem cost_by_drink_type (sequence : List DrinkType) :
  let m_count := (sequence.filter (fun x => x = 'M')).length
  let l_count := (sequence.filter (fun x => x = 'L')).length
  sequence.length > 0 →
  calculate_milk_tea_cost sequence ≤ (m_count * 3) + (l_count * 4) :=
sorry
-- </vc-theorems>