-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def correctTail (body tail : String) : Bool := sorry

theorem correct_tail_when_ends_with (body tail : String) 
  (h : String.endsWith body tail = true) : 
  correctTail body tail = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem correct_tail_when_not_ends_with (body tail : String)
  (h : String.endsWith body tail = false) :
  correctTail body tail = false := sorry

theorem correct_tail_single_char (body tail : String)
  (h : tail.length = 1) :
  correctTail body tail = (body.back = tail.front) := sorry

theorem correct_tail_reflexive (text : String) :
  correctTail text text = true := sorry

theorem correct_tail_empty_strings : 
  correctTail "" "" = true := sorry

theorem correct_tail_empty_tail (x : String) :
  correctTail x "" = true := sorry

theorem correct_tail_empty_body (x : String) :
  correctTail "" x = false := sorry
-- </vc-theorems>