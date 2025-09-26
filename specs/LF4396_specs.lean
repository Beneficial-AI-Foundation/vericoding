-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zipvalidate (s : String) : Bool := sorry 

theorem length_property (s : String) : 
  s.length ≠ 6 → zipvalidate s = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digit_property (s : String) :
  s.length = 6 → (∃ c ∈ s.data, !c.isDigit) → zipvalidate s = false := sorry

theorem first_digit_property (n : Nat) :
  let s := toString n
  s.length = 6 → 
  (s.get 0 = '0' ∨ 
   s.get 0 = '5' ∨
   s.get 0 = '7' ∨ 
   s.get 0 = '8' ∨
   s.get 0 = '9') →
  zipvalidate s = false := sorry
-- </vc-theorems>