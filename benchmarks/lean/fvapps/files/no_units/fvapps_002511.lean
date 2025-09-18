-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_stack_cubes (nums : List Nat) : String := sorry

private def isSorted (l : List Nat) : Bool := 
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x ≥ y && isSorted (y::rest)
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_list_always_stackable (nums : List Nat) : 
  nums ≠ [] → isSorted nums → can_stack_cubes nums = "Yes" := sorry

theorem output_is_yes_or_no (nums : List Nat) :
  nums ≠ [] → can_stack_cubes nums = "Yes" ∨ can_stack_cubes nums = "No" := sorry

theorem small_lists_stackable (nums : List Nat) :
  nums ≠ [] → List.length nums ≤ 2 → can_stack_cubes nums = "Yes" := sorry

theorem edge_cases :
  can_stack_cubes [1] = "Yes" ∧
  can_stack_cubes [1, 1] = "Yes" ∧ 
  can_stack_cubes [2, 1] = "Yes" ∧
  can_stack_cubes [1, 2, 1] = "No" := sorry
-- </vc-theorems>