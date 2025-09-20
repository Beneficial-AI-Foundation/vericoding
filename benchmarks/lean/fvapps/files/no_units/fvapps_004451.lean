-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_a_b (numbers : List Int) (c : Int) : Option (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_a_b_properties {numbers : List Int} {c : Int} (h : numbers.length ≥ 2) :
  match find_a_b numbers c with
  | none => True 
  | some (a, b) => 
    a ∈ numbers ∧ 
    b ∈ numbers ∧
    a * b = c ∧
    ∃ i j, i < j ∧ 
          numbers.get? i = some a ∧
          numbers.get? j = some b :=
  sorry

theorem find_a_b_exists_for_product {numbers : List Int} (h : numbers.length ≥ 2) :
  let i := numbers.length / 2
  let a := numbers[0]'(by sorry)
  let b := numbers[i]'(by sorry)
  let c := a * b
  ∃ x y, find_a_b numbers c = some (x, y) ∧ x * y = c :=
  sorry

theorem find_a_b_order {numbers : List Int} (h : numbers.length ≥ 2) :
  let i := numbers.length / 2
  let a := numbers[i]'(by sorry)
  let b := numbers[0]'(by sorry)
  let c := a * b
  match find_a_b numbers c with
  | none => True
  | some (x, y) =>
    ∃ i j, i < j ∧
          numbers.get? i = some x ∧
          numbers.get? j = some y :=
  sorry
-- </vc-theorems>