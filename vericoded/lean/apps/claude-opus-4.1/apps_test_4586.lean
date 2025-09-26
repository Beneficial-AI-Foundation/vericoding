import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  1000 ≤ N ∧ N ≤ 9999

def ExtractDigits (N : Int) (h : ValidInput N) : Int × Int × Int × Int :=
  let d1 := N / 1000
  let d2 := (N / 100) % 10
  let d3 := (N / 10) % 10
  let d4 := N % 10
  (d1, d2, d3, d4)

def IsGood (N : Int) (h : ValidInput N) : Prop :=
  let (d1, d2, d3, d4) := ExtractDigits N h
  (d1 = d2 ∧ d2 = d3) ∨ (d2 = d3 ∧ d3 = d4)

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance isGood_decidable (N : Int) (h : ValidInput N) : Decidable (IsGood N h) := by
  unfold IsGood ExtractDigits
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : String :=
  if IsGood N h_precond then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : String) (h_precond : solve_precond N) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ IsGood N h_precond)

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  unfold solve_postcond solve
  split_ifs with h
  · -- Case: IsGood N h_precond is true
    constructor
    · left; rfl
    · constructor
      · intro _; exact h
      · intro _; rfl
  · -- Case: IsGood N h_precond is false
    constructor
    · right; rfl
    · constructor
      · intro h_eq; contradiction
      · intro h_good; contradiction
-- </vc-theorems>
