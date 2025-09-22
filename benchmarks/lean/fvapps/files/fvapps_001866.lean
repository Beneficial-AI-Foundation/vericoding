-- <vc-preamble>
def sum (xs : List Nat) : Nat := 
  match xs with
  | [] => 0
  | h :: t => h + sum t

def sumOfLists (xss : List (List Nat)) : Nat :=
  sum (xss.map sum)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_maximum_gold (grid : List (List Nat)) : Nat := sorry 

theorem result_less_than_total (grid : List (List Nat)) :
  get_maximum_gold grid ≤ sumOfLists grid := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_grid_is_zero {w h : Nat} (grid : List (List Nat)) 
  (h1 : grid.length = h)
  (h2 : ∀ row ∈ grid, row.length = w ∧ ∀ x ∈ row, x = 0) :
  get_maximum_gold grid = 0 := sorry

theorem result_is_non_negative (grid : List (List Nat)) :
  get_maximum_gold grid ≥ 0 := sorry

theorem grid_unchanged (grid original : List (List Nat)) :
  original = grid →
  get_maximum_gold grid = get_maximum_gold grid ∧ grid = original := sorry

theorem single_value {w h val : Nat} (grid : List (List Nat))
  (h1 : grid.length = h)
  (h2 : ∀ row ∈ grid, row.length = w)
  (h3 : grid.head!.head! = val)
  (h4 : ∀ (i j : Nat), (i,j) ≠ (0,0) → 
    i < h → j < w → (grid.get! i).get! j = 0) :
  get_maximum_gold grid = val := sorry

theorem max_path_viable (grid : List (List Nat)) :
  get_maximum_gold grid ≤ sumOfLists grid := sorry
-- </vc-theorems>