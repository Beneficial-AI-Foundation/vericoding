-- <vc-preamble>
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)
termination_by n
decreasing_by 
  have h1 : n ≥ 10 := by omega
  have h2 : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
  exact h2

def ValidInput (N : Int) : Prop :=
  N ≥ 1

def F (a b : Int) : Nat :=
  let digitsA := numDigits (Int.natAbs a)
  let digitsB := numDigits (Int.natAbs b)
  if digitsA > digitsB then digitsA else digitsB

def IsFactorPair (a b N : Int) : Prop :=
  a ≥ 1 ∧ b ≥ 1 ∧ a * b = N

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (_ : solve_precond N) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : Int) (h_precond : solve_precond N) : Prop :=
  result ≥ 1 ∧ 
  (∃ a b, IsFactorPair a b N ∧ result = Int.ofNat (F a b)) ∧
  (∀ a b, IsFactorPair a b N → result ≤ Int.ofNat (F a b))

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>