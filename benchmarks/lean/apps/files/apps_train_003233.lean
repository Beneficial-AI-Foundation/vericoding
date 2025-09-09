-- <vc-helpers>
-- </vc-helpers>

def calculate (a : Float) (op : String) (b : Float) : Option Float := sorry

inductive IsValidOp : String → Prop where
  | plus : IsValidOp "+"
  | minus : IsValidOp "-"
  | times : IsValidOp "*"
  | divide : IsValidOp "/"

theorem calculate_valid_ops {a b : Float} {op : String} (h : IsValidOp op) :
  match op with
  | "+" => calculate a op b = some (a + b)
  | "-" => calculate a op b = some (a - b)
  | "*" => calculate a op b = some (a * b)
  | "/" => match Float.toString b with
           | "0" => calculate a op b = none 
           | _ => calculate a op b = some (a / b)
  | _ => True
  := sorry

theorem calculate_invalid_ops {a b : Float} {op : String} (h : ¬IsValidOp op) :
  calculate a op b = none := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate 2 "+" 4

/-
info: -7
-/
-- #guard_msgs in
-- #eval calculate 49 "/" -7

/-
info: None
-/
-- #guard_msgs in
-- #eval calculate 8 "m" 2

-- Apps difficulty: introductory
-- Assurance level: unguarded