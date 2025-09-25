-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_captains_room (k : Nat) (rooms : List Nat) : Nat := sorry

-- Main property theorems
-- </vc-definitions>

-- <vc-theorems>
theorem find_captains_room_properties 
  (k : Nat) (regular_rooms : List Nat) (captain_room : Nat)
  (h1 : k ≥ 2) (h2 : k ≤ 20)
  (h3 : ∀ r ∈ regular_rooms, r ≥ 1 ∧ r ≤ 50)
  (h4 : captain_room ≥ 51) (h5 : captain_room ≤ 100)
  (h6 : captain_room ∉ regular_rooms) :
  let room_numbers := (regular_rooms.map (λ r => List.replicate k r)).join ++ [captain_room] 
  have result := find_captains_room k room_numbers
  -- Main assertions
  find_captains_room k room_numbers = captain_room ∧ 
  (room_numbers.filter (λ x => x = find_captains_room k room_numbers)).length = 1 ∧
  -- k copies of regular rooms
  ∀ room ∈ regular_rooms, 
    (room_numbers.filter (λ x => x = room)).length = k := sorry

-- Minimal case theorem

theorem find_captains_room_minimal_case
  (k : Nat) (h1 : k ≥ 2) (h2 : k ≤ 20) :
  find_captains_room k (List.replicate k 1 ++ [2]) = 2 := sorry
-- </vc-theorems>