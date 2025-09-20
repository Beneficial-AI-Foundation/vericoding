-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_sold_values (arr : Array Nat) : Array Nat := sorry

theorem output_length_matches_input (arr : Array Nat) :
  (find_min_sold_values arr).size = arr.size := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_never_increases_by_more_than_one (arr : Array Nat) (i : Nat) :
  i > 0 → i < (find_min_sold_values arr).size →
  match (find_min_sold_values arr).get? (i-1), (find_min_sold_values arr).get? i with
  | some prev, some curr => 
    curr ≥ prev - 1 ∧ curr ≤ prev + 1
  | _, _ => True
  := sorry

theorem output_elements_never_exceed_input (arr : Array Nat) (i : Nat) :
  i < arr.size →
  match (find_min_sold_values arr).get? i, arr.get? i with 
  | some result, some input => result ≤ input
  | _, _ => True
  := sorry

theorem minimum_element_preserved (arr : Array Nat) (min : Nat) :
  arr.size ≥ 2 →
  (∀ i, i < arr.size → match arr.get? i with 
    | some x => x ≥ min
    | none => True) →
  (∃ i, i < arr.size ∧ match arr.get? i with
    | some x => x = min
    | none => False) →
  (∃ i, i < (find_min_sold_values arr).size ∧ 
    match (find_min_sold_values arr).get? i with
    | some x => x = min
    | none => False)
  := sorry
-- </vc-theorems>