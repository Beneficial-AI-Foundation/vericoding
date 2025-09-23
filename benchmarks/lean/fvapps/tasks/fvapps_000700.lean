-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>