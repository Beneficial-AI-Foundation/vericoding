-- <vc-preamble>
def create_linked_list {α} (values : List α) : Option (Node α) := sorry

def linked_list_to_list {α} (node : Option (Node α)) : List α := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_list_to_parts {α} (head : Option (Node α)) (k : Nat) : List (Option (Node α)) := sorry

theorem split_list_returns_k_parts {α} (values : List α) (k : Nat) (h : k > 0) :
  let head := create_linked_list values
  let result := split_list_to_parts head k
  result.length = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_list_preserves_elements {α} (values : List α) (k : Nat) (h : k > 0) :
  let head := create_linked_list values
  let result := split_list_to_parts head k
  List.join (result.map linked_list_to_list) = values := sorry

theorem split_list_balanced_sizes {α} (values : List α) (k : Nat) (h : k > 0) :
  let head := create_linked_list values
  let result := split_list_to_parts head k
  let non_empty := (result.map linked_list_to_list).filter (fun l => ¬l.isEmpty)
  ¬non_empty.isEmpty →
  (List.maximum? (non_empty.map List.length)).get! - 
  (List.minimum? (non_empty.map List.length)).get! ≤ 1 := sorry

theorem empty_list_split {α} (k : Nat) (h : k > 0) :
  let result := split_list_to_parts (none : Option (Node α)) k
  result.length = k ∧ 
  result.all (fun x => x.isNone) := sorry

theorem single_part_split {α} (values : List α) (h : values ≠ []) :
  let head := create_linked_list values
  let result := split_list_to_parts head 1
  result.length = 1 ∧
  linked_list_to_list result[0]! = values := sorry
-- </vc-theorems>