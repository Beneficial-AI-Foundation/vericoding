-- <vc-preamble>
def hill_jumping_competition (n : Nat) (heights : List Nat) (operations : List (List Nat)) : List Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_operation (op : List Nat) : Bool :=
match op with
| h::t => 
  if h = 1 then t.length = 2 && List.head! t ≥ 1 && List.get! t 1 ≥ 1
  else if h = 2 then t.length = 3 && List.head! t ≥ 1 && List.get! t 1 ≥ List.head! t
  else false
| [] => false
-- </vc-definitions>

-- <vc-theorems>
theorem hill_jumping_result_length (n : Nat) (heights : List Nat) (operations : List (List Nat)) :
  List.all operations is_valid_operation →
  (hill_jumping_competition n heights operations).length = 
    (List.filter (fun op => List.head! op = 1) operations).length := 
sorry

theorem hill_jumping_bounds (n : Nat) (heights : List Nat) (operations : List (List Nat)) :
  List.all operations is_valid_operation →
  List.all (hill_jumping_competition n heights operations) (fun x => x ≥ 1 ∧ x ≤ n) :=
sorry

theorem hill_jumping_preserves_heights (n : Nat) (heights : List Nat) (operations : List (List Nat)) :
  List.all operations is_valid_operation →
  let original := heights
  let _ := hill_jumping_competition n heights operations
  heights = original :=
sorry

/-
info: [3, 4]
-/
-- #guard_msgs in
-- #eval hill_jumping_competition 5 [1, 2, 3, 4, 5] [[1, 1, 2], [2, 3, 4, -1], [1, 1, 2]]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval hill_jumping_competition 3 [1, 3, 2] [[1, 1, 1], [2, 1, 2, 1], [1, 1, 1]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded