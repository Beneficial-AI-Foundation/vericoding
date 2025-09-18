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
-- </vc-theorems>