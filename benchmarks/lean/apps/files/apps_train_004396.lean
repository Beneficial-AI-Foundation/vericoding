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

/-
info: True
-/
-- #guard_msgs in
-- #eval zipvalidate "142784"

/-
info: True
-/
-- #guard_msgs in
-- #eval zipvalidate "642784"

/-
info: False
-/
-- #guard_msgs in
-- #eval zipvalidate "111"

/-
info: False
-/
-- #guard_msgs in
-- #eval zipvalidate "555555"

/-
info: False
-/
-- #guard_msgs in
-- #eval zipvalidate "@68345"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded