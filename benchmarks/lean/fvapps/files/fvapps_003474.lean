-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findPartMaxProd (n : Nat) : List (List Nat) × Nat := sorry

def sumList : List Nat → Nat
  | [] => 0
  | x::xs => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem find_part_max_prod_output_structure (n : Nat) (h : n > 0) (h2 : n ≤ 1000) :
  let result := findPartMaxProd n
  if n = 1 then
    result = ([[1]], 1) 
  else if n % 3 = 1 then 
    result.1.length = 2 ∧
    (∀ x ∈ result.1, x.length > 0)
  else
    result.1.length = 1 ∧
    result.1.head?.isSome := sorry

theorem find_part_max_prod_sum_equals_input (n : Nat) (h : n > 0) (h2 : n ≤ 1000) :
  let result := findPartMaxProd n
  ∀ parts ∈ result.1, sumList parts = n := sorry

theorem find_part_max_prod_parts_valid (n : Nat) (h : n > 0) (h2 : n ≤ 1000) :
  let result := findPartMaxProd n
  n = 1 ∨
  (∀ parts ∈ result.1,
    (∀ x ∈ parts, x = 2 ∨ x = 3 ∨ x = 4) ∧ 
    ((parts.filter (· = 4)).length ≤ 1)) := sorry
-- </vc-theorems>