-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countsubsetsum (target : Nat) (arr : List Nat) : Nat := sorry

def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem zero_sum_always_has_one_solution {arr : List Nat} : 
  countsubsetsum 0 arr = 1 := sorry

theorem single_element_sums {arr : List Nat} {x : Nat} :
  x ∈ arr → countsubsetsum x arr ≥ 1 := sorry

theorem results_non_negative {target : Nat} {arr : List Nat} :
  countsubsetsum target arr ≥ 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_test_case 4 16 [2, 4, 6, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_test_case 4 20 [2, 8, 12, 10]
-- </vc-theorems>