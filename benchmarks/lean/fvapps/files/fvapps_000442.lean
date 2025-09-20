-- <vc-preamble>
def list_maximum (l: List Nat) : Nat :=
match l with
| [] => 0
| [x] => x
| x::xs => max x (list_maximum xs)

def list_sum (l: List Nat) : Nat :=
match l with
| [] => 0
| x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_difficulty (difficulties: List Nat) (days: Nat) : Int :=
sorry

def list_sort (l: List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_difficulty_invalid_days {difficulties : List Nat} {days : Nat} :
  days > difficulties.length → min_difficulty difficulties days = -1
  :=
sorry

theorem min_difficulty_lb_max {difficulties : List Nat} {days : Nat} :
  days ≤ difficulties.length →
  min_difficulty difficulties days ≥ 0 →
  min_difficulty difficulties days ≥ list_maximum difficulties
  :=
sorry

theorem min_difficulty_lb_sum_min {difficulties : List Nat} {days : Nat} :
  days ≤ difficulties.length →
  min_difficulty difficulties days ≥ 0 →
  min_difficulty difficulties days ≥ list_sum (List.take days (list_sort difficulties))
  :=
sorry

theorem min_difficulty_single_day {difficulties : List Nat} :
  difficulties.length > 0 →
  min_difficulty difficulties 1 = list_maximum difficulties
  :=
sorry

theorem min_difficulty_monotonic {difficulties : List Nat} {days : Nat} :
  days > 1 →
  days ≤ difficulties.length →
  min_difficulty difficulties days ≥ 0 →
  min_difficulty difficulties (days-1) ≥ 0 →
  min_difficulty difficulties days ≥ min_difficulty difficulties (days-1)
  :=
sorry
-- </vc-theorems>