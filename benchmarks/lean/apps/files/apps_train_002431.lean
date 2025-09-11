-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lemonade_change (bills : List Nat) : Bool := sorry

def countChange (state : Nat × Nat) (bill : Nat) : Nat × Nat :=
  match bill with
  | 5 => (state.1 + 1, state.2)
  | 10 => (state.1 - 1, state.2 + 1)
  | _ => if state.2 ≥ 1 ∧ state.1 ≥ 1 
        then (state.1 - 1, state.2 - 1)
        else (state.1 - 3, state.2)
-- </vc-definitions>

-- <vc-theorems>
theorem lemonade_change_success 
  {bills : List Nat} 
  (h : lemonade_change bills = true) :
  ∀ p : List Nat, List.isPrefixOf p bills →
  (let state := List.foldl countChange (0, 0) p;
   state.1 ≥ 0 ∧ state.2 ≥ 0) := sorry

theorem lemonade_change_failure  
  {bills : List Nat}
  (h : lemonade_change bills = false) :
  ∃ p : List Nat, List.isPrefixOf p bills ∧
  (let state := List.foldl countChange (0, 0) p;
   state.1 < 0 ∨ state.2 < 0) := sorry

theorem lemonade_change_empty :
  lemonade_change [] = true := sorry

theorem lemonade_change_all_fives (n : Nat) :
  lemonade_change (List.replicate n 5) = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval lemonade_change [5, 5, 5, 10, 20]

/-
info: True
-/
-- #guard_msgs in
-- #eval lemonade_change [5, 5, 10]

/-
info: False
-/
-- #guard_msgs in
-- #eval lemonade_change [5, 5, 10, 10, 20]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded