-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def show_me {α : Type} (obj : α) : String := sorry

class SingleAttr where
  attr : String
deriving Inhabited

class TestClass where
  a : Nat 
  b : Nat
  c : Nat
deriving Inhabited
-- </vc-definitions>

-- <vc-theorems>
theorem single_attribute {attr_name : String} (h : attr_name ≠ "") :
  let obj := SingleAttr.mk attr_name
  let result := show_me obj
  result.contains (attr_name.get ⟨0⟩) ∧ ¬result.contains '&' := sorry

theorem multiple_attributes :
  let obj := TestClass.mk 1 2 3
  let result := show_me obj
  result.startsWith "Hi, I'm one of those TestClasss!" ∧ 
  result.contains '&' ∧
  result.contains 'a' ∧ 
  result.contains 'b' ∧
  result.contains 'c' ∧
  result.endsWith "a, b and c." := sorry
-- </vc-theorems>