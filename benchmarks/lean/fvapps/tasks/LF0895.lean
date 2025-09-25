-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_numbers_between_strings (n1 n2 : Int) (use_floor_division : Bool) : Int :=
  sorry

-- Property: Regular addition when use_floor_division is false
-- </vc-definitions>

-- <vc-theorems>
theorem add_numbers_reg_addition {n1 n2 : Int} : 
  add_numbers_between_strings n1 n2 false = n1 + n2 := 
  sorry

-- Property: Floor division when use_floor_division is true and n2 ≠ 0

theorem add_numbers_floor_div {n1 n2 : Int} (h : n2 ≠ 0) :
  add_numbers_between_strings n1 n2 true = n1 / n2 :=
  sorry

-- Property: Division by zero results in failure

theorem add_numbers_div_zero_fails {n1 : Int} :
  ¬∃ (result : Int), add_numbers_between_strings n1 0 true = result :=
  sorry
-- </vc-theorems>