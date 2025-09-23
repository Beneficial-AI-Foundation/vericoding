-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem test_empty_pop {α : Type} (plates : DinnerPlates α) (cap : Nat)
    (h : cap > 0) (h2 : cap ≤ 100) :
    plates.pop = none := sorry

theorem test_push_pop_sequence {α : Type} (plates : DinnerPlates α) 
    (cap : Nat) (values : List α)
    (h : cap > 0) (h2 : cap ≤ 10) (h3 : values.length > 0) (h4 : values.length ≤ 20) :
    ∀ v ∈ values, plates.pop = some v ∨ plates.pop = none := sorry

theorem test_pop_at_stack {α : Type} (plates : DinnerPlates α)
    (cap : Nat) (values : List α) (stackIdx : Nat)
    (h : cap > 0) (h2 : cap ≤ 10) (h3 : values.length > 0) 
    (h4 : values.length ≤ 20) (h5 : stackIdx ≤ 5) :
    plates.stacks ≠ [] →
    ∃ v, plates.popAtStack stackIdx = some v ∧ v ∈ values ∨ plates.popAtStack stackIdx = none := sorry

theorem test_sequential_operations {α : Type} (plates : DinnerPlates α)
    (cap : Nat) (values : List α)
    (h : cap > 0) (h2 : cap ≤ 10) (h3 : values.length ≤ 20) :
    values.length > 2 →
    ∃ v, plates.pop = some v ∧ v ∈ values ∨ plates.pop = none := sorry
-- </vc-theorems>