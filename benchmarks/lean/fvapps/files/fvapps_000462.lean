-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_reach (arr : Array Nat) (start : Nat) : Bool := sorry

theorem start_within_bounds {arr : Array Nat} {start : Nat} :
  start ≥ arr.size → can_reach arr start = false := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>