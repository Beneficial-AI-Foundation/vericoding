-- <vc-preamble>
-- Helper function for extracting numbers (axiomatized)
noncomputable axiom ExtractNumbers : String → Nat → List Int → String → List Int

def ValidInputFormat (input : String) : Prop :=
  input.length > 0 ∧ 
  let nums := ExtractNumbers input 0 [] ""
  nums.length ≥ 3 ∧ 
  (∀ i, 0 ≤ i ∧ i < 3 → 1 ≤ nums.get! i ∧ nums.get! i ≤ 100)

noncomputable def ParseThreeIntsFunc (input : String) (h1 : input.length > 0) (h2 : ValidInputFormat input) : Int × Int × Int :=
  let nums := ExtractNumbers input 0 [] ""
  (nums.get! 0, nums.get! 1, nums.get! 2)

def CanDistributeEqually (a b c : Int) : Prop :=
  a + b = c ∨ b + c = a ∨ c + a = b

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInputFormat input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let h1 := h_precond.1
  let h2 := h_precond.2
  let numbers := ParseThreeIntsFunc input h1 h2
  let a := numbers.1
  let b := numbers.2.1  
  let c := numbers.2.2
  (result = "Yes\n" ∨ result = "No\n") ∧
  (result = "Yes\n" ↔ CanDistributeEqually a b c) ∧
  (numbers.1 ≥ 1 ∧ numbers.2.1 ≥ 1 ∧ numbers.2.2 ≥ 1 ∧
   numbers.1 ≤ 100 ∧ numbers.2.1 ≤ 100 ∧ numbers.2.2 ≤ 100)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>