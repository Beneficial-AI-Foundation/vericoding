/-
You have stumbled across the divine pleasure that is owning a dog and a garden. Now time to pick up all the cr@p! :D

Given a 2D array to represent your garden, you must find and collect all of the dog cr@p - represented by '@'.

You will also be given the number of bags you have access to (bags), and the capactity of a bag (cap). If there are no bags then you can't pick anything up, so you can ignore cap.

You need to find out if you have enough capacity to collect all the cr@p and make your garden clean again. 

If you do, return 'Clean', else return 'Cr@p'.

Watch out though - if your dog is out there ('D'), he gets very touchy about being watched. If he is there you need to return 'Dog!!'.

For example:

x=
[[\_,\_,\_,\_,\_,\_]
 [\_,\_,\_,\_,@,\_]
 [@,\_,\_,\_,\_,\_]]

bags = 2, cap = 2

return  --> 'Clean'
-/

def crap (garden : List (List Cell)) (bags : Nat) (cap : Nat) : GardenResult :=
  sorry

def countCrap (garden : List (List Cell)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def hasDog (garden : List (List Cell)) : Bool :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded