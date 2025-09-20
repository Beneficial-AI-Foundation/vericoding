-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_recipe_book (n : Nat) : List (List Nat) := sorry

def format_output (groups : List (List Nat)) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_recipe_book_returns_lists {n : Nat} (h : n > 0) (h2 : n ≤ 1000) :
  let result := solve_recipe_book n
  ∀ x ∈ result, ∀ y ∈ x, y > 0 := sorry

theorem solve_recipe_book_contains_one {n : Nat} (h : n > 0) (h2 : n ≤ 1000) :
  let result := solve_recipe_book n
  result ≠ [] → 1 ∈ result.head! := sorry 

theorem solve_recipe_book_no_duplicates_in_groups {n : Nat} (h : n > 0) (h2 : n ≤ 1000) :
  let result := solve_recipe_book n  
  ∀ group ∈ result, ∀ x y, x ∈ group → y ∈ group → x = y → x = y := sorry

theorem solve_recipe_book_optimal_groups {n : Nat} (h : n > 1) (h2 : n ≤ 1000) :
  let result := solve_recipe_book n
  result.length ≤ (n + 1) / 2 := sorry

theorem format_output_valid {groups : List (List Nat)} :
  let result := format_output groups
  (∀ x ∈ result, x.length > 0) ∧
  result.length = groups.length + 1 ∧
  result.head! = toString groups.length := sorry
-- </vc-theorems>