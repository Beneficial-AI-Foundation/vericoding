-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findStartingJuiceShop (juices : List Nat) (distances : List Nat) : Int := sorry

theorem empty_input_result : 
  (juices : List Nat) → (distances : List Nat) →
  juices.length = 0 ∨ distances.length = 0 →
  findStartingJuiceShop juices distances = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_index_result :
  (juices : List Nat) → (distances : List Nat) →
  juices.length = distances.length →
  let result := findStartingJuiceShop juices distances
  result = -1 ∨ (0 ≤ result ∧ result < juices.length) := sorry

theorem solution_properties :
  (juices : List Nat) → (distances : List Nat) →
  juices.length = distances.length →
  juices.length > 0 →
  let result := findStartingJuiceShop juices distances
  result ≠ -1 →
  ∀ i : Nat, i < juices.length →
    let startPos := result.toNat
    let currentPos := (startPos + i) % juices.length
    let remainingJuice := (List.range i).foldl
      (fun acc j => 
        let pos := (startPos + j) % juices.length
        acc + juices[pos]! - distances[pos]!)
      0
    i < juices.length - 1 → remainingJuice ≥ 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_starting_juice_shop [1, 10, 3] [5, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_starting_juice_shop [5, 2, 3] [4, 3, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_starting_juice_shop [1, 2, 3] [4, 5, 6]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded