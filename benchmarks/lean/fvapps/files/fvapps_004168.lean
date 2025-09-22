-- <vc-preamble>
def abs (n : Int) : Nat := 
  if n ≥ 0 then n.toNat else (-n).toNat

def sum (l : List Nat) : Nat :=
  l.foldl (·+·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elevator_distance (floors : List Int) : Nat := sorry

theorem elevator_distance_non_negative (floors : List Int) 
  (h : floors.length ≥ 2) : 
  elevator_distance floors ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem elevator_distance_reversal (floors : List Int)
  (h : floors.length ≥ 2) :
  elevator_distance floors = elevator_distance floors.reverse := sorry

theorem elevator_distance_same_floor (n : Int) :
  elevator_distance [n, n] = 0 := sorry

theorem elevator_distance_all_zero (n : Nat) 
  (h : n ≥ 2) :
  elevator_distance (List.replicate n 0) = 0 := sorry

theorem elevator_distance_up_down : 
  elevator_distance [1, -1] = 2 := sorry
-- </vc-theorems>