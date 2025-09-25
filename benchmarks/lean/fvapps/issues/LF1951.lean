-- <vc-preamble>
def List.maximum (l : List Nat) : Option Nat := 
  sorry 

def List.minimum (l : List Nat) : Option Nat := 
  sorry

def time_to_get_free (payload : List Nat) (floor : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def State.hook (s : State) (floor : Nat) (a b : Nat) : State :=
  sorry 

-- Empty payload should take 0 time
-- </vc-definitions>

-- <vc-theorems>
theorem time_to_get_free_empty (floor : Nat) : 
  time_to_get_free [] floor = 0 := sorry

-- Properties of time_to_get_free

theorem time_to_get_free_properties {payload : List Nat} {floor : Nat}
  (h1 : payload.length > 0)
  (h2 : ∀ x ∈ payload, x > 0 ∧ x ≤ 10) :
  let result := time_to_get_free payload floor
  -- Result is non-negative
  (result ≥ 0) ∧ 
  -- Result is at least difference of max/min payload
  (result ≥ ((List.maximum payload).getD 0 - (List.minimum payload).getD 0)) ∧
  -- Result is at least minimum distance to floor
  (result ≥ min (floor - (List.minimum payload).getD 0) 
              (floor - (List.maximum payload).getD 0)) := sorry

-- Properties of State.hook

theorem state_hook_properties {s : State} {floor a b : Nat}
  (h1 : a > 0 ∧ a ≤ 10)
  (h2 : b > 0 ∧ b ≤ 10) :
  let newState := s.hook floor a b
  -- Time is non-negative
  (newState.time ≥ 0) ∧
  -- b is in new payload
  (b ∈ newState.payload) ∧
  -- New payload size is bounded
  (newState.payload.length ≤ s.payload.length + 1) := sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve 2 [(3, 5), (5, 3)]

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve 2 [(5, 3), (3, 5)]

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve 1 [(1, 9)]
-- </vc-theorems>