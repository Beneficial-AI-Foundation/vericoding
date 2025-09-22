-- <vc-preamble>
def mymin (x y : Int) : Int :=
  if x ≤ y then x else y

def ValidInput (k a b v : Int) : Prop :=
  2 ≤ k ∧ k ≤ 1000 ∧ 1 ≤ a ∧ a ≤ 1000 ∧ 1 ≤ b ∧ b ≤ 1000 ∧ 1 ≤ v ∧ v ≤ 1000

def BoxCapacity (numBoxes k b v : Int) : Int :=
  v * (numBoxes + mymin b ((k - 1) * numBoxes))

def CanStoreNuts (numBoxes k a b v : Int) : Prop :=
  a ≤ BoxCapacity numBoxes k b v

def IsMinimalSolution (result k a b v : Int) : Prop :=
  CanStoreNuts result k a b v ∧
  (result = 1 ∨ ¬CanStoreNuts (result - 1) k a b v)

@[reducible, simp]
def solve_precond (k a b v : Int) : Prop :=
  ValidInput k a b v
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k a b v : Int) (h_precond : solve_precond k a b v) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k a b v : Int) (result: Int) (h_precond : solve_precond k a b v) : Prop :=
  result ≥ 1 ∧
  result ≤ 1009 ∧
  IsMinimalSolution result k a b v ∧
  ∃ i, 1 ≤ i ∧ i ≤ 1009 ∧ CanStoreNuts i k a b v ∧ result = i ∧
  (∀ j, 1 ≤ j ∧ j < i → ¬CanStoreNuts j k a b v)

theorem solve_spec_satisfied (k a b v : Int) (h_precond : solve_precond k a b v) :
    solve_postcond k a b v (solve k a b v h_precond) h_precond := by
  sorry
-- </vc-theorems>