-- <vc-preamble>
def func (numbers : List Nat) : List (Nat ⊕ String) := sorry

def toBinary (n : Nat) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toOctal (n : Nat) : String := sorry
def toHex (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem conversion_properties {numbers : List Nat} (h : numbers.length > 0) :
  let result := func numbers
  let expected_n := numbers.foldl (· + ·) 0 / numbers.length
  List.get! result 0 = .inl expected_n ∧ 
  List.get! result 1 = .inr (toBinary expected_n) ∧
  List.get! result 2 = .inr (toOctal expected_n) ∧
  List.get! result 3 = .inr (toHex expected_n) := sorry

theorem length_properties {numbers : List Nat} (h : numbers.length > 0) :
  let result := func numbers
  result.length = 4 ∧
  (match List.get! result 0 with | .inl _ => true | .inr _ => false) ∧
  (∀ i, i > 0 → i < 4 → match List.get! result i with | .inl _ => false | .inr _ => true) := sorry

theorem zero_case {numbers : List Nat} (h : numbers.length > 0) 
    (h' : ∀ x ∈ numbers, x = 0) :
  func numbers = [.inl 0, .inr "0", .inr "0", .inr "0"] := sorry
-- </vc-theorems>