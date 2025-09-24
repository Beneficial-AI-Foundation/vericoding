-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (x: Float) (op: Operation) (y: Float) : Option Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculator_valid_ops {x y : Float} {op : Operation} :
  let result := calculate x op y
  match op with
  | Operation.add => result = some (x + y)
  | Operation.sub => result = some (x - y) 
  | Operation.mul => result = some (x * y)
  | Operation.div => result = some (x / y) ∨ result = none
  := sorry

theorem calculator_div_by_zero {x : Float} :
  calculate x Operation.div 0 = none := sorry

theorem calculator_outputs_valid {x y : Float} {op : Operation} :
  ∃ (r: Float), calculate x op y = some r ∨ calculate x op y = none := sorry

/-
info: 11.2
-/
-- #guard_msgs in
-- #eval calculate 3.2 "+" 8

/-
info: None
-/
-- #guard_msgs in
-- #eval calculate -3 "/" 0

/-
info: None
-/
-- #guard_msgs in
-- #eval calculate -3 "w" 1
-- </vc-theorems>