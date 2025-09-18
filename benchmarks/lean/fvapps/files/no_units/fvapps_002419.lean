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
-- </vc-theorems>