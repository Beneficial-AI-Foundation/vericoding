-- <vc-preamble>
def xor_fold (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => t.foldl Nat.xor h

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => h + list_sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_xor_sum (n : Nat) (arr : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_xor_sum_length {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  List.length result = 0 ∨ List.length result = 2 :=
sorry

theorem solve_xor_sum_verifies {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let full_arr := arr ++ result
  list_sum full_arr = 2 * xor_fold full_arr :=
sorry

theorem solve_xor_sum_bounds {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let total := list_sum arr
  ∀ x ∈ result, x ≥ 0 ∧ x ≤ 2 * total :=
sorry
-- </vc-theorems>