-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arithmetic_operations (a b : Int) : String := sorry

theorem arithmetic_operations_format 
  (a b : Int) : 
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  lines.length = 3 ∧ 
  lines.all (fun line => (line.drop (if line.front = '-' then 1 else 0)).all Char.isDigit)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_operations_values
  (a b : Int) :
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  let sum_val := lines[0]!.toInt!
  let diff_val := lines[1]!.toInt!
  let prod_val := lines[2]!.toInt!
  sum_val = a + b ∧
  diff_val = a - b ∧ 
  prod_val = a * b
  := sorry

theorem arithmetic_operations_positive
  (a b : Int)
  (ha : 0 ≤ a) (hb : 0 ≤ b)
  (ha_bound : a ≤ 1000) (hb_bound : b ≤ 1000) :
  let result := arithmetic_operations a b
  let lines := result.splitOn "\n"
  let sum_val := lines[0]!.toInt!
  let prod_val := lines[2]!.toInt!
  sum_val ≥ a ∧
  prod_val ≥ min a b
  := sorry
-- </vc-theorems>