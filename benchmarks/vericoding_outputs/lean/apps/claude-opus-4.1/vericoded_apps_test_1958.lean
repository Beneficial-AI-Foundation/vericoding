import Mathlib
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
-- LLM HELPER
lemma computePaymentBackward_nonneg (buyers : List String) (p : Int) (hp : p ≥ 2) : 
    ∀ k currentApples, currentApples ≥ 0 → computePaymentBackward buyers p k currentApples ≥ 0 := by
  intro k
  induction k with
  | zero => 
    intro currentApples hApples
    simp [computePaymentBackward]
    split
    next h => 
      split
      next h2 =>
        -- halfplus case: payment = (currentApples * 2 + 1) / 2 * p
        have newApples := currentApples * 2 + 1
        have payment := newApples / 2 * p
        apply Int.mul_nonneg
        · apply Int.ediv_nonneg
          · linarith
          · norm_num
        · linarith
      next h2 =>
        -- half case: payment = currentApples * p
        apply Int.mul_nonneg <;> linarith
    next h => 
      -- empty list case
      rfl
  | succ k' ih =>
    intro currentApples hApples
    simp [computePaymentBackward]
    split
    next h =>
      split
      next h2 =>
        -- halfplus case
        have newApples := currentApples * 2 + 1
        apply Int.add_nonneg
        · apply Int.mul_nonneg
          · apply Int.ediv_nonneg
            · linarith
            · norm_num
          · linarith
        · apply ih
          linarith
      next h2 =>
        -- half case
        apply Int.add_nonneg
        · apply Int.mul_nonneg <;> linarith
        · apply ih
          linarith
    next h =>
      -- index out of bounds
      rfl

-- LLM HELPER
lemma computeTotalPayment_nonneg (buyers : List String) (p : Int) (hp : p ≥ 2) :
    computeTotalPayment buyers p ≥ 0 := by
  simp [computeTotalPayment]
  split
  next h =>
    apply computePaymentBackward_nonneg
    · exact hp
    · linarith
  next h =>
    rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n p : Int) (buyers : List String) (h_precond : solve_precond n p buyers) : Int :=
  computeTotalPayment buyers p
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n p : Int) (buyers : List String) (result : Int) (h_precond : solve_precond n p buyers) : Prop :=
  result ≥ 0 ∧ result = computeTotalPayment buyers p

theorem solve_spec_satisfied (n p : Int) (buyers : List String) (h_precond : solve_precond n p buyers) :
    solve_postcond n p buyers (solve n p buyers h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · have hp : p ≥ 2 := by
      unfold solve_precond ValidInput at h_precond
      obtain ⟨_, _, hp, _, _, _, _⟩ := h_precond
      exact hp
    exact computeTotalPayment_nonneg buyers p hp
  · rfl
-- </vc-theorems>
