-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_reorder_doubled (lst : List Int) : Bool := sorry

def count_occurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0
-- </vc-definitions>

-- <vc-theorems>
theorem reorder_doubled_count_property (lst : List Int) :
  can_reorder_doubled lst = true → lst ≠ [] →
    ∀ n ∈ lst, n ≠ 0 →
      (2 * n) ∈ lst ∧ count_occurrences (2 * n) lst ≥ count_occurrences n lst := sorry

theorem single_numbers_not_doubled {numbers : List Int} (h : ∀ n ∈ numbers, n ≠ 0) :
  can_reorder_doubled (numbers ++ [0]) = false := sorry

theorem empty_list_property :
  can_reorder_doubled [] = true := sorry

theorem all_zeros_property (n : Nat) :
  can_reorder_doubled (List.replicate n 0) = true := sorry
-- </vc-theorems>