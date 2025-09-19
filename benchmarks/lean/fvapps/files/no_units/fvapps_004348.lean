-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) : α := sorry

theorem solution_in_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (0 ≤ index ∧ index < items.length) → 
  solution items index default = items.get! index.toNat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_negative_in_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (-items.length ≤ index ∧ index < 0) → 
  solution items index default = items.get! (items.length + index.toNat) := sorry

theorem solution_out_of_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (index < -items.length ∨ index ≥ items.length) → 
  solution items index default = default := sorry

theorem empty_list {α : Type} [Inhabited α] (default : α) :
  ∀ (index : Int), solution ([] : List α) index default = default := sorry

theorem list_bounds {α : Type} [Inhabited α] (items : List α) (default : α) 
  (h : items ≠ []) :
  solution items items.length default = default ∧
  solution items (-items.length - 1) default = default ∧
  solution items (items.length - 1) default = items.getLast h ∧
  solution items (-items.length) default = items.head! := sorry
-- </vc-theorems>