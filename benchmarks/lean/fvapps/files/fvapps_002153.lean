-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def create_maze (T : Nat) : Nat × Nat × Nat × List (Nat × Nat × Nat × Nat) :=
sorry

def is_valid_door (door : Nat × Nat × Nat × Nat) (n m : Nat) : Bool :=
sorry

def are_doors_unique (doors : List (Nat × Nat × Nat × Nat)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimal_maze_properties (T : Nat) (h : T > 0) (h2 : T ≤ 5) :
  let (n, m, k, doors) := create_maze T
  n = 4 ∧
  m = 4 ∧
  k ≥ 3 ∧
  k ≤ 6 :=
sorry

theorem large_maze_properties (T : Nat) (h : T ≥ 6^4) (h2 : T < 6^5) :
  let (n, m, k, doors) := create_maze T
  n = 12 ∧
  m = 12 :=
sorry
-- </vc-theorems>