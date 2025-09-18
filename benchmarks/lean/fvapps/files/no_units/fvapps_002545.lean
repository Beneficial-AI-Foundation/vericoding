-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def no_order (s : String) : Option Int := sorry

theorem no_order_returns_option_int (expr : String) :
  match no_order expr with
  | some n => True 
  | none => True
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_order_whitespace_is_none (spaces : String) 
  (h : ∀ c ∈ spaces.data, c = ' ') :
  no_order spaces = none := sorry

theorem no_order_none_input :
  no_order "" = none := sorry

theorem no_order_division_by_zero :
  no_order "5/0" = none ∧ 
  no_order "10+5/0" = none := sorry

theorem no_order_invalid_exprs :
  no_order "++" = none ∧
  no_order "5++5" = none ∧
  no_order "abc" = none ∧
  no_order "" = none := sorry
-- </vc-theorems>