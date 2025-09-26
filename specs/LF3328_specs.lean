-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def delete_nth (lst: List Int) (max_e: Nat) : List Int := sorry

theorem delete_nth_length {lst: List Int} {max_e: Nat} :
  List.length (delete_nth lst max_e) ≤ List.length lst := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delete_nth_max_occurrences {lst: List Int} {max_e: Nat} {x: Int} :
  x ∈ delete_nth lst max_e → List.count x (delete_nth lst max_e) ≤ max_e := sorry

theorem delete_nth_elements_from_original {lst: List Int} {max_e: Nat} {x: Int} :
  x ∈ delete_nth lst max_e → x ∈ lst := sorry 

theorem delete_nth_zero {lst: List Int} :
  delete_nth lst 0 = [] := sorry

theorem delete_nth_empty {lst: List Int} {max_e: Nat} :
  lst = [] → delete_nth lst max_e = [] := sorry

theorem delete_nth_preserves_first {lst: List Int} {max_e: Nat} :
  max_e > 0 → ∀ x, x ∈ lst → x ∈ delete_nth lst max_e := sorry
-- </vc-theorems>