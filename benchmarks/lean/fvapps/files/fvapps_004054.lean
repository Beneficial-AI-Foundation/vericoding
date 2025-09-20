-- <vc-preamble>
def List.minimum (l : List Nat) (h : l ≠ []) : Nat :=
match l with
| [] => by contradiction
| x::xs => xs.foldl min x

def List.maximum (l : List Nat) (h : l ≠ []) : Nat :=
match l with
| [] => by contradiction
| x::xs => xs.foldl max x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def differenceInAges (ages : List Nat) : Nat × Nat × Nat := sorry

theorem difference_in_ages_basic_properties
  (ages : List Nat) (h : ages ≠ []) :
  let result := differenceInAges ages
  List.minimum ages h = result.1 ∧
  List.maximum ages h = result.2.1 ∧
  result.2.2 = result.2.1 - result.1 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem difference_in_ages_difference_nonnegative
  (ages : List Nat) (h : ages ≠ []) :
  let result := differenceInAges ages
  result.2.2 ≥ 0 :=
sorry

theorem difference_in_ages_youngest_leq_oldest
  (ages : List Nat) (h : ages ≠ []) :
  let result := differenceInAges ages
  result.1 ≤ result.2.1 :=
sorry

theorem difference_in_ages_same_values
  (ages : List Nat) (h : ages ≠ []) (x : Nat) 
  (h2 : ∀ n, n ∈ ages → n = x) :
  let result := differenceInAges ages
  result.1 = result.2.1 ∧
  result.2.2 = 0 :=
sorry
-- </vc-theorems>