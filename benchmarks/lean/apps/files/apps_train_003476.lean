-- <vc-preamble>
def four_piles (n : Nat) (y : Nat) : Option (List Nat) := sorry

def sum_list : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum_list t
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth : List Nat → Nat → Option Nat 
  | [], _ => none
  | (h :: t), 0 => some h
  | (h :: t), n+1 => nth t n
-- </vc-definitions>

-- <vc-theorems>
theorem four_piles_properties_solution (n y : Nat) (h1 : n > 0) (h2 : y > 0) (h3 : y ≤ 100) : 
  match four_piles n y with
  | some result => 
    -- Result has length 4
    result.length = 4 ∧ 
    -- Elements follow x+y, x-y, x*y, x/y pattern for some x
    ∃ x : Nat, 
      (nth result 0 = some (x + y)) ∧
      (nth result 1 = some (x - y)) ∧
      (nth result 2 = some (x * y)) ∧
      (nth result 3 = some (x / y)) ∧
    -- Elements are positive
    (∀ i ∈ result, i > 0) ∧
    -- Sum equals input n  
    sum_list result = n
  | none =>
    -- If no solution, divmod has remainder
    let prod := n * y
    let denom := (y + 1) * (y + 1)
    prod % denom ≠ 0 ∨ (prod / denom = y)
  := sorry

theorem four_piles_properties_positive (n y : Nat) (h1 : n > 0) (h2 : y > 0) :
  match four_piles n y with
  | some result => ∀ x ∈ result, x > 0
  | none => True
  := sorry

theorem four_piles_properties_sum (n y : Nat) (h1 : n > 0) (h2 : y > 0) :
  match four_piles n y with
  | some result => sum_list result = n  
  | none => True
  := sorry

/-
info: [12, 6, 27, 3]
-/
-- #guard_msgs in
-- #eval four_piles 48 3

/-
info: [20, 12, 64, 4]
-/
-- #guard_msgs in
-- #eval four_piles 100 4

/-
info: []
-/
-- #guard_msgs in
-- #eval four_piles 25 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded