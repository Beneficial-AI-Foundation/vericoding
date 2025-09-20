-- <vc-preamble>
structure BridgeProblemInputs where
  n : Nat
  m : Nat
  islands : List (List Int)
  bridges : List Int
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_bridge_problem (n m : Nat) (islands : List (List Int)) (bridges : List Int) : String :=
sorry

def verify_bridge_placement (bridges : List Int) (gaps : List (Int × Int)) (result : String) : Bool :=
sorry

def string_to_nat_array (s : String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def get_indices (result : String) : List Nat :=
  if result = "No" then []
  else string_to_nat_array (result.splitOn "\n").head!

theorem result_format_valid (n m : Nat) (islands : List (List Int)) (bridges : List Int) :
  let result := solve_bridge_problem n m islands bridges
  (result = "No") ∨
  (∃ nums : List Nat, result = s!"Yes\n{nums}" ∧ nums.length = n - 1) :=
sorry

theorem bridge_placement_valid (n m : Nat) (islands : List (List Int)) (bridges : List Int) :
  let result := solve_bridge_problem n m islands bridges
  let gaps := List.range (n-1) |>.map (λ i => (1, 1))
  verify_bridge_placement bridges gaps result = true :=
sorry

theorem bridge_indices_valid (n m : Nat) (islands : List (List Int)) (bridges : List Int) :
  let result := solve_bridge_problem n m islands bridges
  let indices := get_indices result
  result = "No" ∨
  (∀ i ∈ indices, 1 ≤ i ∧ i ≤ m) :=
sorry
-- </vc-theorems>