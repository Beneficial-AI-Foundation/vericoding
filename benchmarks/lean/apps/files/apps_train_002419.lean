-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distanceBetweenBusStops (distance : List Nat) (start dest : Nat) : Nat := sorry 

def sumList : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem distance_symmetric {distance : List Nat} {start dest : Nat} 
  (h : distance.length > 0) :
  distanceBetweenBusStops distance start dest = 
  distanceBetweenBusStops distance dest start := sorry

theorem distance_nonnegative {distance : List Nat} {start dest : Nat}
  (h : distance.length > 0) :
  distanceBetweenBusStops distance start dest ≥ 0 := sorry

theorem same_stop_zero {distance : List Nat} {start : Nat}
  (h : distance.length > 0) :
  distanceBetweenBusStops distance start start = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval distanceBetweenBusStops [1, 2, 3, 4] 0 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval distanceBetweenBusStops [1, 2, 3, 4] 0 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval distanceBetweenBusStops [1, 2, 3, 4] 0 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible