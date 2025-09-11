-- <vc-preamble>
def solve_xor_sum (n : Nat) (arr : List Nat) : List Nat := sorry

def xor_fold (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => t.foldl Nat.xor h
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | h::t => h + list_sum t
-- </vc-definitions>

-- <vc-theorems>
theorem solve_xor_sum_length {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  List.length result = 0 ∨ List.length result = 2 := sorry

theorem solve_xor_sum_verifies {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let full_arr := arr ++ result
  list_sum full_arr = 2 * xor_fold full_arr := sorry

theorem solve_xor_sum_bounds {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let total := list_sum arr
  ∀ x ∈ result, x ≥ 0 ∧ x ≤ 2 * total := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval solve_xor_sum 4 [1, 2, 3, 6]

/-
info: 2
-/
-- #guard_msgs in
-- #eval len solve_xor_sum(1, [8])

/-
info: 2 * (arr[0] ^ arr[1] ^ arr[2])
-/
-- #guard_msgs in
-- #eval sum [8] + result

/-
info: 2 * xor
-/
-- #guard_msgs in
-- #eval sum [1, 1] + result
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded