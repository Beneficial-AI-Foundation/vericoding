-- <vc-preamble>
def Grid := List (List Char)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rock_puzzle (n m : Nat) : Grid × (Nat × Nat) :=
sorry

def count_arrows (grid : Grid) : Nat :=
sorry

def is_square_grid (grid : Grid) : Bool :=
sorry

def valid_start_pos (pos : Nat × Nat) (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_rock_puzzle_dimensions {n : Nat} (h : n > 0) :
  let (grid, start_pos) := solve_rock_puzzle n n
  List.length grid = n ∧
  is_square_grid grid = true ∧
  valid_start_pos start_pos n = true :=
sorry

theorem valid_characters {n : Nat} (h : n > 0) :
  let (grid, _) := solve_rock_puzzle n n
  ∀ (i : Nat), i < List.length grid →
  ∀ (j : Nat), j < List.length (List.get! grid i) →
  let c := List.get! (List.get! grid i) j
  c = '^' ∨ c = 'v' ∨ c = '<' ∨ c = '>' ∨ c = '.' :=
sorry

theorem has_arrows {n : Nat} (h : n > 0) :
  let (grid, _) := solve_rock_puzzle n n
  count_arrows grid > 0 :=
sorry
-- </vc-theorems>