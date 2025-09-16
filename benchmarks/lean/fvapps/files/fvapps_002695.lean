-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.isSorted {α : Type} [Ord α] : List α → Prop := sorry

def sect_sort (xs : List α) (start : Nat) (length : Option Nat := none) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sect_sort_length {α : Type} [Ord α] (xs : List α) (start : Nat) (length : Option Nat) :
  List.length (sect_sort xs start length) = List.length xs := sorry

theorem sect_sort_prefix {α : Type} [Ord α] (xs : List α) (start : Nat) (length : Option Nat) :
  (sect_sort xs start length).take start = xs.take start := sorry

theorem sect_sort_suffix {α : Type} [Ord α] (xs : List α) (start : Nat) (length : Option Nat) 
    (h : let endIdx := min (start + (length.getD (xs.length - start))) xs.length; True) :
  let endIdx := min (start + (length.getD (xs.length - start))) xs.length
  (sect_sort xs start length).drop endIdx = xs.drop endIdx := sorry

theorem sect_sort_middle_sorted {α : Type} [Ord α] (xs : List α) (start : Nat) (length : Option Nat)
    (h : let endIdx := min (start + (length.getD (xs.length - start))) xs.length; True) :
  let endIdx := min (start + (length.getD (xs.length - start))) xs.length
  List.isSorted ((sect_sort xs start length).drop start) := sorry

theorem sect_sort_empty {α : Type} [Ord α] (start : Nat) (length : Option Nat) :
  sect_sort ([] : List α) start length = [] := sorry

theorem sect_sort_start_exceeds_length {α : Type} [Ord α] (xs : List α) (start : Nat) (length : Option Nat) :
  start ≥ xs.length → sect_sort xs start length = xs := sorry

/-
info: [1, 2, 3, 4, 5, 6, 7, 8, 9]
-/
-- #guard_msgs in
-- #eval sect_sort [1, 2, 5, 7, 4, 6, 3, 9, 8] 2

/-
info: [9, 7, 1, 2, 3, 4, 5, 8, 6]
-/
-- #guard_msgs in
-- #eval sect_sort [9, 7, 4, 2, 5, 3, 1, 8, 6] 2 5

/-
info: []
-/
-- #guard_msgs in
-- #eval sect_sort [] 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded