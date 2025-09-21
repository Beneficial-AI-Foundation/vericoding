-- <vc-preamble>
def ValidCosts (c : Array Int) : Prop :=
  c.size = 4 ∧
  c[0]! ≥ 1 ∧ c[1]! ≥ 1 ∧ c[2]! ≥ 1 ∧ c[3]! ≥ 1 ∧
  c[0]! ≤ 1000 ∧ c[1]! ≤ 1000 ∧ c[2]! ≤ 1000 ∧ c[3]! ≤ 1000

def ValidRides (rides : Array Int) : Prop :=
  rides.size ≥ 1 ∧ rides.size ≤ 1000 ∧
  ∀ i, 0 ≤ i ∧ i < rides.size → 0 ≤ rides[i]! ∧ rides[i]! ≤ 1000

def sum_array (arr : List Int) : Int :=
  arr.sum

partial def min_with_unlimited (rides : List Int) (current_cost : Int) (individual_cost : Int) (unlimited_cost : Int) (index : Int) : Int :=
  if index ≥ rides.length then current_cost
  else 
    let new_cost := current_cost - rides[index.toNat]! * individual_cost + unlimited_cost
    let updated_cost := if new_cost < current_cost ∧ new_cost ≥ 0 then new_cost else current_cost
    min_with_unlimited rides updated_cost individual_cost unlimited_cost (index + 1)

def optimized_cost (rides : List Int) (individual_cost : Int) (unlimited_cost : Int) : Int :=
  let initial_cost := sum_array rides * individual_cost
  min_with_unlimited rides initial_cost individual_cost unlimited_cost 0

def min5 (a b c d e : Int) : Int :=
  min (min (min (min a b) c) d) e

def CorrectResult (c : Array Int) (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result = min5 (optimized_cost a.toList c[0]! c[1]! + optimized_cost b.toList c[0]! c[1]!)
                (optimized_cost a.toList c[0]! c[1]! + c[2]!)
                (optimized_cost b.toList c[0]! c[1]! + c[2]!)
                (c[2]! + c[2]!)
                c[3]!

@[reducible, simp]
def solve_precond (c : Array Int) (a : Array Int) (b : Array Int) : Prop :=
  ValidCosts c ∧ ValidRides a ∧ ValidRides b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (c : Array Int) (a : Array Int) (b : Array Int) (h_precond : solve_precond c a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (c : Array Int) (a : Array Int) (b : Array Int) (result : Int) (h_precond : solve_precond c a b) : Prop :=
  result ≥ 0 ∧ 
  CorrectResult c a b result ∧
  result ≤ min5 (sum_array a.toList * c[0]! + sum_array b.toList * c[0]!)
                (sum_array a.toList * c[0]! + c[2]!)
                (sum_array b.toList * c[0]! + c[2]!)
                (c[2]! + c[2]!)
                c[3]!

theorem solve_spec_satisfied (c : Array Int) (a : Array Int) (b : Array Int) (h_precond : solve_precond c a b) :
    solve_postcond c a b (solve c a b h_precond) h_precond := by
  sorry
-- </vc-theorems>