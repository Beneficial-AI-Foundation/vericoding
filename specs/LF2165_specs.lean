-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_perm_sort (perm : List Nat) : Bool := sorry

theorem identity_permutation_valid {n : Nat} (perm : List Nat)
  (h : perm = List.range n) : 
  solve_perm_sort perm = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_boolean (perm : List Nat) :
  solve_perm_sort perm = true ∨ solve_perm_sort perm = false := sorry 

theorem reversed_sequence_property {n : Nat} (perm : List Nat) 
  (h : perm = (List.range n).reverse) :
  solve_perm_sort perm = (n ≤ 3) := sorry
-- </vc-theorems>