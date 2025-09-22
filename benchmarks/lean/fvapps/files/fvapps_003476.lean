-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | (h :: t) => h + sum_list t

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | (h :: t), 0 => some h
  | (h :: t), n+1 => nth t n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def four_piles (n : Nat) (y : Nat) : Option (List Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem four_piles_properties_solution (n y : Nat) (h1 : n > 0) (h2 : y > 0) (h3 : y ≤ 100) :
  match four_piles n y with
  | some result =>

    result.length = 4 ∧

    ∃ x : Nat,
      (nth result 0 = some (x + y)) ∧
      (nth result 1 = some (x - y)) ∧
      (nth result 2 = some (x * y)) ∧
      (nth result 3 = some (x / y)) ∧

    (∀ i ∈ result, i > 0) ∧

    sum_list result = n
  | none =>

    let prod := n * y
    let denom := (y + 1) * (y + 1)
    prod % denom ≠ 0 ∨ (prod / denom = y)
  :=
sorry

theorem four_piles_properties_positive (n y : Nat) (h1 : n > 0) (h2 : y > 0) :
  match four_piles n y with
  | some result => ∀ x ∈ result, x > 0
  | none => True
  :=
sorry

theorem four_piles_properties_sum (n y : Nat) (h1 : n > 0) (h2 : y > 0) :
  match four_piles n y with
  | some result => sum_list result = n
  | none => True
  :=
sorry
-- </vc-theorems>