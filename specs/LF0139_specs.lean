-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numRescueBoats (people : List Nat) (limit : Nat) : Nat :=
  sorry

def listMax (l : List Nat) : Nat :=
  sorry

def listMin (l : List Nat) : Nat :=
  sorry

def listSort (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rescue_boats_minimum (people : List Nat) (h : people ≠ []) :
  let limit := listMax people
  numRescueBoats people limit ≥ (people.length + 1) / 2 := by
  sorry

theorem rescue_boats_maximum (people : List Nat) (h : people ≠ []) :
  let limit := listMax people
  numRescueBoats people limit ≤ people.length := by
  sorry

theorem rescue_boats_deterministic (people : List Nat) (h : people ≠ []) :
  let limit := listMax people
  numRescueBoats people limit = numRescueBoats people limit := by
  sorry

theorem single_person_per_boat (weights : List Nat) (h : weights ≠ []) :
  let min_limit := listMin weights
  numRescueBoats weights min_limit = weights.length := by
  sorry

theorem sorted_same_result (people : List Nat) (limit : Nat)
    (h1 : people.length ≥ 2) (h2 : ∀ x ∈ people, x ≤ 100) (h3 : limit ≤ 100) :
  numRescueBoats people limit = numRescueBoats (listSort people) limit := by
  sorry
-- </vc-theorems>