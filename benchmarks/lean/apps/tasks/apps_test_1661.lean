-- <vc-preamble>
def countBuyableGames : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | g :: gs, b :: bs => 
      if b ≥ g then 1 + countBuyableGames gs bs
      else countBuyableGames gs (b :: bs)

def ValidInput (n m : Int) (games bills : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧
  games.length = n.natAbs ∧ bills.length = m.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < games.length → 1 ≤ games[i]! ∧ games[i]! ≤ 1000) ∧
  (∀ i, 0 ≤ i ∧ i < bills.length → 1 ≤ bills[i]! ∧ bills[i]! ≤ 1000)

@[reducible, simp]
def solve_precond (n m : Int) (games bills : List Int) : Prop :=
  ValidInput n m games bills
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (games bills : List Int) (h_precond : solve_precond n m games bills) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (games bills : List Int) (result : Int) (h_precond : solve_precond n m games bills) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result ≤ m ∧ result = countBuyableGames games bills

theorem solve_spec_satisfied (n m : Int) (games bills : List Int) (h_precond : solve_precond n m games bills) :
    solve_postcond n m games bills (solve n m games bills h_precond) h_precond := by
  sorry
-- </vc-theorems>