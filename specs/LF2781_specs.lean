-- <vc-preamble>
def crap (garden : List (List Cell)) (bags : Nat) (cap : Nat) : GardenResult :=
  sorry

def countCrap (garden : List (List Cell)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasDog (garden : List (List Cell)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem crap_result_always_valid (garden : List (List Cell)) (bags cap : Nat) :
  let result := crap garden bags cap
  result = GardenResult.Clean ∨ result = GardenResult.Crap ∨ result = GardenResult.Dog :=
  sorry

theorem dog_implies_dog_result (garden : List (List Cell)) (bags cap : Nat) :
  hasDog garden → crap garden bags cap = GardenResult.Dog :=
  sorry

theorem clean_implies_sufficient_capacity (garden : List (List Cell)) (bags cap : Nat) :
  crap garden bags cap = GardenResult.Clean →
  countCrap garden ≤ bags * cap :=
  sorry

theorem crap_implies_insufficient_capacity (garden : List (List Cell)) (bags cap : Nat) :
  crap garden bags cap = GardenResult.Crap →
  countCrap garden > bags * cap :=
  sorry

theorem zero_capacity_behavior (garden : List (List Cell)) :
  ¬hasDog garden →
  (crap garden 0 0 = GardenResult.Clean ↔ countCrap garden = 0) ∧
  (crap garden 0 0 = GardenResult.Crap ↔ countCrap garden > 0) :=
  sorry

/-
info: 'Clean'
-/
-- #guard_msgs in
-- #eval crap [["_", "_", "_", "_"], ["_", "_", "_", "@"], ["_", "_", "@", "_"]] 2 2

/-
info: 'Dog!!'
-/
-- #guard_msgs in
-- #eval crap [["_", "_"], ["_", "@"], ["D", "_"]] 2 2

/-
info: 'Clean'
-/
-- #guard_msgs in
-- #eval crap [["@", "@"], ["@", "@"], ["@", "@"]] 3 2
-- </vc-theorems>