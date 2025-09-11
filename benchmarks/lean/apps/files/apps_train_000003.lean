-- <vc-preamble>
def max_water_difference (n : Nat) (k : Nat) (barrels : List Nat) : Nat :=
  sorry

/- Helper function to sum a list -/

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/- Helper function to sort list descending -/

def sortDescending (l : List Nat) : List Nat :=
  sorry

/- Helper function to get maximum of non-empty list -/

def listMaximum : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: xs => if x > listMaximum xs then x else listMaximum xs

/- Helper function to take first n elements -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def takeFront : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | n+1, x :: xs => x :: takeFront n xs

/- max_water_difference returns sum of k+1 largest values -/
-- </vc-definitions>

-- <vc-theorems>
theorem max_water_diff_equals_k_plus_one_largest
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  max_water_difference n k barrels = 
    listSum (takeFront (k+1) (sortDescending barrels)) :=
  sorry

/- max_water_difference result is greater than or equal to max barrel -/

theorem max_water_diff_ge_max_barrel
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n)
  (h₃ : barrels ≠ []) :
  max_water_difference n k barrels ≥ listMaximum barrels :=
  sorry

/- max_water_difference result is less than or equal to sum of all barrels -/

theorem max_water_diff_le_total_sum
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  max_water_difference n k barrels ≤ listSum barrels :=
  sorry

/- max_water_difference does not modify input list -/

theorem max_water_diff_preserves_input
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  let original := barrels
  let _ := max_water_difference n k barrels
  barrels = original :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval max_water_difference 4 1 [5, 5, 5, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_water_difference 3 2 [0, 0, 0]

/-
info: 12
-/
-- #guard_msgs in
-- #eval max_water_difference 5 2 [1, 2, 3, 4, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded