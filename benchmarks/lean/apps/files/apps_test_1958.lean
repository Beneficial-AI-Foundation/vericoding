-- <vc-preamble>
def ValidInput (n p : Int) (buyers : List String) : Prop :=
  1 ≤ n ∧ n ≤ 40 ∧
  2 ≤ p ∧ p ≤ 1000 ∧
  p % 2 = 0 ∧
  buyers.length = n ∧
  ∀ i, 0 ≤ i ∧ i < buyers.length → buyers[i]! = "half" ∨ buyers[i]! = "halfplus"

def computePaymentBackward (buyers : List String) (p : Int) : Nat → Int → Int
  | 0, currentApples => 
      if buyers.length > 0 then
        let newApples := if buyers[0]! = "halfplus" then 
                          currentApples * 2 + 1
                         else 
                          currentApples * 2
        let payment := if buyers[0]! = "halfplus" then 
                        (newApples / 2) * p
                       else 
                        currentApples * p
        payment
      else 0
  | currentIndex + 1, currentApples =>
      if currentIndex + 1 < buyers.length then
        let newApples := if buyers[currentIndex + 1]! = "halfplus" then 
                          currentApples * 2 + 1
                         else 
                          currentApples * 2
        let payment := if buyers[currentIndex + 1]! = "halfplus" then 
                        (newApples / 2) * p
                       else 
                        currentApples * p
        payment + computePaymentBackward buyers p currentIndex newApples
      else 0

def computeTotalPayment (buyers : List String) (p : Int) : Int :=
  if buyers.length > 0 then
    computePaymentBackward buyers p (buyers.length - 1) 0
  else 0

@[reducible, simp]
def solve_precond (n p : Int) (buyers : List String) : Prop :=
  ValidInput n p buyers
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n p : Int) (buyers : List String) (h_precond : solve_precond n p buyers) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n p : Int) (buyers : List String) (result : Int) (h_precond : solve_precond n p buyers) : Prop :=
  result ≥ 0 ∧ result = computeTotalPayment buyers p

theorem solve_spec_satisfied (n p : Int) (buyers : List String) (h_precond : solve_precond n p buyers) :
    solve_postcond n p buyers (solve n p buyers h_precond) h_precond := by
  sorry
-- </vc-theorems>