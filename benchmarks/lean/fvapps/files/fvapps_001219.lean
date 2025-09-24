-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_treasure_distances (n m : Nat) (treasures blocked : List (Nat × Nat)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dimensions_correct (n m : Nat) (h1 : n ≥ 2) (h2 : m ≥ 2) :
  let treasures := [(1,1)]
  let blocked := []
  let result := find_treasure_distances n m treasures blocked
  List.length result = n ∧ 
  ∀ row ∈ result, List.length (String.split row (· = ' ')) = m :=
sorry

theorem treasure_is_zero (n m : Nat) (h1 : n ≥ 2) (h2 : m ≥ 2) :
  let treasures := [(1,1)]
  let blocked := []
  let result := find_treasure_distances n m treasures blocked
  List.head! (String.split (List.head! result) (· = ' ')) = "0" :=
sorry

theorem no_X_when_unblocked (n m : Nat) (h1 : n ≥ 2) (h2 : m ≥ 2) :
  let treasures := [(1,1)]
  let blocked := []
  let result := find_treasure_distances n m treasures blocked
  ∀ row ∈ result, ¬String.contains row 'X' := 
sorry

theorem adjacent_differ_by_one (n m : Nat) (h1 : n ≥ 2) (h2 : m ≥ 2) :
  let treasures := [(1,1)]
  let blocked := []
  let result := find_treasure_distances n m treasures blocked
  ∀ row ∈ result, ∀ j, j + 1 < m → 
    let vals := List.map String.toNat! (String.split row (· = ' '))
    max (vals[j]! - vals[j+1]!) (vals[j+1]! - vals[j]!) ≤ 1 :=
sorry

theorem blocked_cells_marked (n m : Nat) (h1 : n ≥ 2) (h2 : m ≥ 2) :
  let treasures := [(1,1)]
  let blocked := [(1,2), (2,1)]
  let result := find_treasure_distances n m treasures blocked
  List.head! (String.split (List.head! result) (· = ' ')) = "0" ∧
  List.get! (String.split (List.head! result) (· = ' ')) 1 = "X" ∧ 
  List.head! (String.split (List.get! result 1) (· = ' ')) = "X" :=
sorry
-- </vc-theorems>