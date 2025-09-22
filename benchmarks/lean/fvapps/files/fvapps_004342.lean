-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat := sorry

def draw_spider (leg_size : Nat) (body_size : Nat) (mouth : Char) (eye : Char) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spider_parentheses_count {leg_size : Nat} {body_size : Nat} {mouth : Char} {eye : Char}
  (h1 : leg_size ≤ 4) (h2 : body_size ≥ 1) (h3 : body_size ≤ 5)
  (h4 : mouth = 'W' ∨ mouth = 'w')
  (h5 : eye = 'o' ∨ eye = 'O' ∨ eye = '0') :
  let result := draw_spider leg_size body_size mouth eye
  (result.count '(' = body_size) ∧ (result.count ')' = body_size) := sorry

theorem spider_leg_prefixes {leg_size : Nat} {body_size : Nat} {mouth : Char} {eye : Char}
  (h1 : leg_size ≤ 4) 
  (h2 : mouth = 'w') (h3 : eye = 'o') :
  let result := draw_spider leg_size 1 mouth eye
  match leg_size with 
  | 0 => result.startsWith ""
  | 1 => result.startsWith "^"
  | 2 => result.startsWith "/\\"
  | 3 => result.startsWith "/╲"
  | 4 => result.startsWith "╱╲"
  | _ => True
  := sorry
-- </vc-theorems>