import Mathlib
-- <vc-preamble>
def ValidInput (A B C D : Int) : Prop :=
  1 ≤ A ∧ A ≤ 1000 ∧ 1 ≤ B ∧ B ≤ 1000 ∧ 1 ≤ C ∧ C ≤ 1000 ∧ 1 ≤ D ∧ D ≤ 1000

def MinTotalFare (A B C D : Int) : Int :=
  (if A < B then A else B) + (if C < D then C else D)

@[reducible, simp]
def solve_precond (A B C D : Int) : Prop :=
  ValidInput A B C D
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
The expression `if a < b then a else b` is equivalent to `min a b`.
This lemma is tagged with `@[simp]` to allow the simplifier to automatically
use this equivalence.
-/
@[simp]
lemma if_lt_else_eq_min (a b : Int) : (if a < b then a else b) = min a b := by
  split_ifs with h
  · -- Case `a < b`: `if` expression is `a`. `min a b` is `a`.
    exact (min_eq_left (le_of_lt h)).symm
  · -- Case `¬(a < b)` which means `b ≤ a`: `if` expression is `b`. `min a b` is `b`.
    exact (min_eq_right (not_lt.mp h)).symm

-- </vc-helpers>

-- <vc-definitions>
def solve (A B C D : Int) (h_precond : solve_precond A B C D) : Int :=
  min A B + min C D
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C D : Int) (result: Int) (h_precond : solve_precond A B C D) : Prop :=
  result = MinTotalFare A B C D

theorem solve_spec_satisfied (A B C D : Int) (h_precond : solve_precond A B C D) :
    solve_postcond A B C D (solve A B C D h_precond) h_precond := by
  simp [solve, MinTotalFare]
-- </vc-theorems>
