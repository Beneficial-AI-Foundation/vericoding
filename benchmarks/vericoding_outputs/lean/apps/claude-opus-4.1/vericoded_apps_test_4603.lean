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
lemma min_eq_if_le (x y : Int) : min x y = (if x ≤ y then x else y) := by
  simp only [min_def]

-- LLM HELPER  
lemma if_le_eq_if_lt (x y : Int) : (if x ≤ y then x else y) = (if x < y then x else y) := by
  split_ifs with h1 h2 h3
  · rfl
  · -- h1: x ≤ y, ¬h2: ¬(x < y), so x = y
    have : x = y := le_antisymm h1 (not_lt.mp h2)
    rw [this]
  · -- ¬h1: ¬(x ≤ y), h3: x < y, contradiction
    exact absurd h3 (not_lt.mpr (le_of_not_le h1))
  · rfl

lemma solve_eq_MinTotalFare (A B C D : Int) :
    min A B + min C D = MinTotalFare A B C D := by
  unfold MinTotalFare
  simp only [min_eq_if_le]
  rw [if_le_eq_if_lt, if_le_eq_if_lt]
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
  unfold solve_postcond solve
  exact solve_eq_MinTotalFare A B C D
-- </vc-theorems>
