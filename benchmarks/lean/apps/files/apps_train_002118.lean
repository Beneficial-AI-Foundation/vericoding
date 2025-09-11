-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (parents : List Nat) : List Nat := sorry

theorem solve_chain_properties (n : Nat) (parents : List Nat) 
    (h1 : n ≥ 2)
    (h2 : parents = List.range (n-1)) : 
    let result := solve n parents
    -- Result length equals input size
    List.length result = n ∧ 
    -- First element equals last element (symmetry)
    List.get! result 0 = List.get! result (n-1) ∧
    -- All values are non-negative
    ∀ x ∈ result, x ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_star_properties (n : Nat) (parents : List Nat)
    (h1 : n ≥ 2) 
    (h2 : parents = List.replicate (n-1) 1) :
    let result := solve n parents
    -- Result length equals input size
    List.length result = n ∧
    -- All elements are natural numbers
    ∀ x ∈ result, x ≥ 0 := sorry

/-
info: [4, 3, 3]
-/
-- #guard_msgs in
-- #eval solve 3 [1, 1]

/-
info: [5, 8, 9, 8, 5]
-/
-- #guard_msgs in
-- #eval solve 5 [1, 2, 3, 4]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval solve 2 [1]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded