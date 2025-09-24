-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (a : Float) (op : String) (b : Float) : Option Float := sorry

inductive IsValidOp : String → Prop where
  | plus : IsValidOp "+"
  | minus : IsValidOp "-"
  | times : IsValidOp "*"
  | divide : IsValidOp "/"
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>