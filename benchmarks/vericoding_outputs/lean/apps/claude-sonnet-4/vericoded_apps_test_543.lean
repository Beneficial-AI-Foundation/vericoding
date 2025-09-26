import Mathlib
-- <vc-preamble>
def ValidInput (pizzas : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < pizzas.length → pizzas[i]! ≥ 0

def validatePizzaSolution (pizzas : List Int) (index : Nat) (d : Bool) (p : Int) : Bool :=
  if h : index < pizzas.length then
    let requirement := pizzas[index]!
    let newP := if requirement % 2 = 1 then 1 - p else p
    let newD := if requirement % 2 = 0 ∧ p = 1 ∧ requirement = 0 then false else d
    validatePizzaSolution pizzas (index + 1) newD newP
  else
    d ∧ p = 0
termination_by pizzas.length - index

def CanFulfillRequirements (pizzas : List Int) : Prop :=
  validatePizzaSolution pizzas 0 true 0 = true

@[reducible, simp]
def solve_precond (pizzas : List Int) : Prop :=
  ValidInput pizzas
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidability instance for CanFulfillRequirements
instance (pizzas : List Int) : Decidable (CanFulfillRequirements pizzas) := by
  unfold CanFulfillRequirements
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (pizzas : List Int) (_ : solve_precond pizzas) : String :=
  if CanFulfillRequirements pizzas then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (pizzas : List Int) (result : String) (_ : solve_precond pizzas) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ CanFulfillRequirements pizzas)

theorem solve_spec_satisfied (pizzas : List Int) (h_precond : solve_precond pizzas) :
    solve_postcond pizzas (solve pizzas h_precond) h_precond := by
  unfold solve solve_postcond CanFulfillRequirements
  split_ifs with h
  · simp [h]
  · simp [h]
-- </vc-theorems>
