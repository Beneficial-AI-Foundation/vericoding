-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_highest (ls : List Int) : Option (List Int) := sorry

theorem two_highest_length_at_most_2 (ls : List Int) :
  match two_highest ls with
  | none => True
  | some result => result.length ≤ 2
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_highest_elements_from_input (ls : List Int) :
  match two_highest ls with
  | none => True
  | some result => ∀ x ∈ result, x ∈ ls
  := sorry

theorem two_highest_descending_order (ls : List Int) :
  match two_highest ls with
  | none => True
  | some result => result.length ≤ 1 ∨ result[0]! ≥ result[1]!
  := sorry

theorem two_highest_unique_elements (ls : List Int) :
  match two_highest ls with
  | none => True
  | some result => ∀ i j, i < result.length → j < result.length → i ≠ j → result[i]! ≠ result[j]!
  := sorry

theorem two_highest_maximal_elements (ls : List Int) :
  !ls.isEmpty →
  match two_highest ls with
  | none => False
  | some result =>
    (result.length < 2 → ∀ (x y : Int), x ∈ ls ∧ y ∈ ls → x = y) ∧
    (result.length = 2 → 
      (∀ x ∈ ls, x ≤ result[0]!) ∧
      (∀ x ∈ ls, x ≤ result[0]! ∨ x = result[1]!))
  := sorry

theorem two_highest_empty_input :
  two_highest [] = some [] := sorry

theorem two_highest_single_element (x : Int) :
  two_highest [x] = some [x] := sorry
-- </vc-theorems>