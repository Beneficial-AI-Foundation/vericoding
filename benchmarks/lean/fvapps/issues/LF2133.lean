-- <vc-preamble>
def solve_religion_grid (r c : Nat) (grid : Grid) : Answer := sorry

theorem output_format (r c : Nat) (grid : Grid) :
  let result := solve_religion_grid r c grid
  result = "0" ∨ result = "1" ∨ result = "2" ∨ result = "3" ∨ result = "4" ∨ result = "MORTAL" :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def inList {α : Type} (x : α) (xs : List α) : Prop := x ∈ xs

theorem all_p_is_mortal (r c : Nat) (grid : Grid) :
  (∀ (row : List GridChar), inList row grid → 
   ∀ (cell : GridChar), inList cell row → cell = GridChar.P) →
  solve_religion_grid r c grid = "MORTAL" :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_a_is_zero (r c : Nat) (grid : Grid) :
  (∀ (row : List GridChar), inList row grid → 
   ∀ (cell : GridChar), inList cell row → cell = GridChar.A) →
  solve_religion_grid r c grid = "0" :=
sorry

theorem grid_dimensions (r c : Nat) (grid : Grid) :
  List.length grid = r ∧
  (∀ (row : List GridChar), inList row grid → List.length row = c) :=
sorry

theorem valid_chars (r c : Nat) (grid : Grid) :
  ∀ (row : List GridChar), inList row grid → 
  ∀ (cell : GridChar), inList cell row → cell = GridChar.A ∨ cell = GridChar.P :=
sorry

theorem single_cell (r c : Nat) (grid : Grid) :
  r = 1 →
  c = 1 →
  grid ≠ [] →
  grid.head! ≠ [] →
  let result := solve_religion_grid r c grid
  (grid.head!.head! = GridChar.A → result = "0") ∧
  (grid.head!.head! = GridChar.P → result = "MORTAL") :=
sorry

/-
info: '2'
-/
-- #guard_msgs in
-- #eval solve_religion_grid 7 8 ["AAPAAAAA", "PPPPAAAA", "PPPPAAAA", "APAAPPPP", "APAPPAPP", "AAAAPPAP", "AAAAPPAA"]

/-
info: 'MORTAL'
-/
-- #guard_msgs in
-- #eval solve_religion_grid 4 4 ["PPPP", "PPPP", "PPPP", "PPPP"]

/-
info: '0'
-/
-- #guard_msgs in
-- #eval solve_religion_grid 1 1 ["A"]
-- </vc-theorems>