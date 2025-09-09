-- <vc-helpers>
-- </vc-helpers>

def can_reach (arr : Array Nat) (start : Nat) : Bool := sorry

theorem start_within_bounds {arr : Array Nat} {start : Nat} :
  start ≥ arr.size → can_reach arr start = false := sorry

theorem array_contains_zero {arr : Array Nat} {start : Nat} :
  start < arr.size → 
  (∀ x ∈ arr.toList, x ≠ 0) →
  can_reach arr start = false := sorry

theorem reachable_properties {arr : Array Nat} {start : Nat} : 
  start < arr.size →
  (∃ x ∈ arr.toList, x = 0) →
  can_reach arr start = true →
  ∃ path : List Nat, 
    path.head? = some start ∧
    (∃ pos, pos < arr.size ∧ pos ∈ path ∧ arr[pos]! = 0) ∧
    ∀ i j, i + 1 < path.length → j = i + 1 →
      let pos₁ := path[i]!
      let pos₂ := path[j]!
      let jump := arr[pos₁]!
      (pos₂ = pos₁ + jump ∨ pos₂ = pos₁ - jump) ∧
      pos₁ < arr.size ∧ pos₂ < arr.size := sorry 

theorem symmetric_jumps {arr : Array Nat} {start : Nat} :
  start < arr.size →
  can_reach arr start = true →
  let zero_pos := (arr.findIdx? (· = 0)).get!
  can_reach arr zero_pos = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_reach #[4, 2, 3, 0, 3, 1, 2] 5

/-
info: True
-/
-- #guard_msgs in
-- #eval can_reach #[4, 2, 3, 0, 3, 1, 2] 0

/-
info: False
-/
-- #guard_msgs in
-- #eval can_reach #[3, 0, 2, 1, 2] 2

-- Apps difficulty: interview
-- Assurance level: unguarded