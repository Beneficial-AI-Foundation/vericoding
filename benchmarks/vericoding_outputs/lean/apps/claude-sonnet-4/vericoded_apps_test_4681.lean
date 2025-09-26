import Mathlib
-- <vc-preamble>
def Lucas : Nat → Int
  | 0 => 2
  | 1 => 1
  | n + 2 => Lucas (n + 1) + Lucas n

def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 86

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Convert Int to Nat safely given precondition
def intToNat (n : Int) (h : 1 ≤ n) : Nat :=
  Int.natAbs n

-- LLM HELPER: Key lemma about natAbs for positive integers
lemma natAbs_of_pos (n : Int) (h : 1 ≤ n) : n.natAbs = Int.natAbs n := rfl

-- LLM HELPER: Conversion lemma
lemma int_natAbs_eq (n : Int) (h : 1 ≤ n) : Int.natAbs n = n.natAbs := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  Lucas n.natAbs
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result: Int) (h_precond : solve_precond n) : Prop :=
  result = Lucas n.natAbs

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve
  rfl
-- </vc-theorems>
