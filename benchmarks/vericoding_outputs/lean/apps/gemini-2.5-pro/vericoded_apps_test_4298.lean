import Mathlib
-- <vc-preamble>
def ValidInput (N D : Int) : Prop :=
  N ≥ 1 ∧ N ≤ 20 ∧ D ≥ 1 ∧ D ≤ 20

def CoverageRange (position D : Int) : Int × Int :=
  (position - D, position + D)

def TreesCovered (N D inspectors : Int) : Prop :=
  inspectors ≥ 1 ∧ inspectors ≤ N ∧ inspectors = ((N - 1) / (2 * D + 1)) + 1

@[reducible, simp]
def solve_precond (N D : Int) : Prop :=
  ValidInput N D
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def is_a_valid_coverage (N D : Int) (inspectors : Finset Int) : Prop :=
  Finset.Icc 1 N ⊆ inspectors.biUnion (fun p => Finset.Icc (p - D) (p + D))
-- </vc-helpers>

-- <vc-definitions>
def solve (N D : Int) (h_precond : solve_precond N D) : Int :=
  ((N - 1) / (2 * D + 1)) + 1
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
