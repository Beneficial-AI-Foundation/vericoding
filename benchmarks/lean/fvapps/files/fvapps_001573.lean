-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def snail {α : Type} (arr : List (List α)) : List α := sorry

def verify_snail_pattern {α : Type} (arr : List (List α)) (result : List α) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem snail_empty_array {α : Type} : snail ([] : List (List α)) = [] := sorry

theorem snail_empty_nested {α : Type} : snail [[]] = ([] : List α) := sorry

theorem snail_single_element {α : Type} (x : α) : snail [[x]] = [x] := sorry 

theorem snail_length {α : Type} (arr : List (List α)) :
  arr ≠ [] → arr.head! ≠ [] → 
  (snail arr).length = arr.length * (arr.head!).length := sorry

theorem snail_pattern_correct {α : Type} (arr : List (List α)) :
  arr ≠ [] → arr.head! ≠ [] →
  verify_snail_pattern arr (snail arr) = true := sorry

theorem snail_empty_list {α : Type} (arr : List (List α)) :
  arr = [] ∨ arr.head! = [] → snail arr = [] := sorry
-- </vc-theorems>