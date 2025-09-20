-- <vc-preamble>
def isValidDigit (c : Char) : Bool :=
  match c with
  | '0' => true | '1' => true | '2' => true | '3' => true | '4' => true
  | '5' => true | '6' => true | '7' => true | '8' => true | '9' => true
  | '.' => true | '+' => true | '-' => true | '*' => true | '/' => true
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.filter (s : String) (p : Char → Bool) : String := sorry

def calculate_string (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_string_evaluates_expressions
  (n₁ n₂ : Float) (op : Char)
  (h_op : op ∈ ['+', '-', '*', '/'])
  (h_div : op = '/' → n₂ ≠ 0)
  : let expr := s!"{n₁}{op}{n₂}"
    let noisy_expr := s!"abc{expr}xyz!@#"
    let result := calculate_string noisy_expr
    let clean_expr := String.filter expr isValidDigit
    let expected := toString (Float.round (match op with
      | '+' => n₁ + n₂
      | '-' => n₁ - n₂
      | '*' => n₁ * n₂
      | '/' => n₁ / n₂
      | _ => 0))
    result = expected :=
sorry

theorem calculate_string_preserves_single_number
  (n : Int) (h : -1000000 ≤ n ∧ n ≤ 1000000)
  : toString (String.toInt! (calculate_string (toString n))) = toString n :=
sorry
-- </vc-theorems>