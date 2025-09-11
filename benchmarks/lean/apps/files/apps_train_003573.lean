-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculator (x : Float) (y : Float) (op : String) : Float ⊕ String := sorry 

theorem calculator_valid_inputs (x y : Float) (op : String) :
  (op = "+" ∨ op = "-" ∨ op = "*" ∨ op = "/") →
  (op ≠ "/" ∨ y ≠ 0) →
  ∃ (result : Float), calculator x y op = Sum.inl result := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculator_division_by_zero (x y : Float) (op : String) :
  op = "/" ∧ y = 0 →
  calculator x y op = Sum.inr "unknown value" := sorry

theorem calculator_invalid_operator (x y : Float) (op : String) :
  (op ≠ "+" ∧ op ≠ "-" ∧ op ≠ "*" ∧ op ≠ "/") →
  calculator x y op = Sum.inr "unknown value" := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval calculator 6 2 "+"

/-
info: 25
-/
-- #guard_msgs in
-- #eval calculator 5 5 "*"

/-
info: 'unknown value'
-/
-- #guard_msgs in
-- #eval calculator 6 2 "&"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded