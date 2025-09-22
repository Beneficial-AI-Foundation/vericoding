-- <vc-preamble>
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

def listMaximum : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: xs => if x > listMaximum xs then x else listMaximum xs

def takeFront : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | n+1, x :: xs => x :: takeFront n xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_water_difference (n : Nat) (k : Nat) (barrels : List Nat) : Nat :=
  sorry

def sortDescending (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_water_diff_equals_k_plus_one_largest
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  max_water_difference n k barrels =
    listSum (takeFront (k+1) (sortDescending barrels)) :=
sorry

theorem max_water_diff_ge_max_barrel
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n)
  (h₃ : barrels ≠ []) :
  max_water_difference n k barrels ≥ listMaximum barrels :=
sorry

theorem max_water_diff_le_total_sum
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  max_water_difference n k barrels ≤ listSum barrels :=
sorry

theorem max_water_diff_preserves_input
  {n k : Nat} {barrels : List Nat}
  (h₁ : barrels.length = n)
  (h₂ : k < n) :
  let original := barrels
  let _ := max_water_difference n k barrels
  barrels = original :=
sorry
-- </vc-theorems>