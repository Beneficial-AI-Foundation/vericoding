-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_2nd_largest {α : Type u} (arr : List α) : Option α := sorry

theorem find_2nd_largest_mixed_property 
  {α : Type} (arr : List (Int ⊕ String)) :
  let ints := arr.filterMap (fun x => match x with | Sum.inl i => some i | _ => none)
  match find_2nd_largest arr with
  | none => ints.eraseDups.length ≤ 1
  | some x => ints.eraseDups.length > 1 ∧ 
             match x with
             | Sum.inl i => ∃ j, j = i ∧ (ints.eraseDups.filter (fun y => y > j)).length = 1
             | _ => False
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_2nd_largest_ints_property
  (arr : List Int) (h1 : arr.length ≥ 2) (h2 : arr.eraseDups = arr) :
  match find_2nd_largest arr with
  | none => False 
  | some x => ∃ max min : Int, 
             (∀ y ∈ arr, y ≤ max) ∧
             (∀ y ∈ arr, y ≥ min) ∧
             x ≤ max ∧ 
             x ≥ min ∧ 
             x ≠ max
  := sorry

theorem find_2nd_largest_ordering
  (arr : List Int) :
  match find_2nd_largest arr with
  | none => True
  | some x => (arr.eraseDups.filter (fun y => y > x)).length = 1
  := sorry
-- </vc-theorems>