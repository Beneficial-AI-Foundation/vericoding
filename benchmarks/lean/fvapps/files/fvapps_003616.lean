-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def charCheck (text : String) (max_len : Nat) (spaces : Bool) : Bool × String := sorry

theorem charCheck_return_type 
  (text : String) (max_len : Nat) (spaces : Bool) :
  let result := charCheck text max_len spaces
  result.1 = true ∨ result.1 = false ∧ result.2.length ≤ max_len := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem charCheck_with_spaces 
  (text : String) (max_len : Nat) :
  let result := charCheck text max_len true 
  result.2 = text.take max_len ∧ result.1 = (text.length ≤ max_len) := sorry

theorem charCheck_without_spaces
  (text : String) (max_len : Nat) :
  let result := charCheck text max_len false
  let text_no_spaces := text.replace " " ""
  result.2 = text_no_spaces.take max_len ∧ 
  result.1 = (text_no_spaces.length ≤ max_len) := sorry

theorem charCheck_empty_max
  (text : String) :
  let result := charCheck text 0 true
  result.1 = (text.length = 0) ∧
  result.2 = "" := sorry

theorem charCheck_spaces_consistency
  (text : String) :
  let result_with_spaces := charCheck text text.length true
  let result_no_spaces := charCheck text text.length false
  result_with_spaces.2.replace " " "" = result_no_spaces.2 := sorry
-- </vc-theorems>