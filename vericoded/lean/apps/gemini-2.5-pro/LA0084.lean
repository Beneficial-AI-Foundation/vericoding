import Mathlib
-- <vc-preamble>
def ValidInput (n a b c : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100

def myMin (x y : Int) : Int :=
  if x ≤ y then x else y

def myMax (x y : Int) : Int :=
  if x ≥ y then x else y

def MinDistance (n a b c : Int) : Int :=
  if n = 1 then 0 else (n - 1) * myMin a b

@[reducible, simp]
def solve_precond (n a b c : Int) : Prop :=
  ValidInput n a b c
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma myMin_le_myMax (a b c : Int) : myMin a b ≤ myMax a (myMax b c) := by
  trans a
  · unfold myMin
    split_ifs <;> linarith
  · unfold myMax
    split_ifs <;> linarith

-- LLM HELPER
theorem MinDistance_nonneg (n a b c : Int) (h : ValidInput n a b c) : MinDistance n a b c ≥ 0 := by
  unfold MinDistance
  split_ifs with h_n_eq_1
  · linarith
  · rcases h with ⟨hn_ge_1, _, ha_ge_1, _, hb_ge_1, _, _, _⟩
    apply mul_nonneg
    · linarith [hn_ge_1]
    · rw [myMin]
      split_ifs <;> linarith [ha_ge_1, hb_ge_1]
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b c : Int) (h_precond : solve_precond n a b c) : Int :=
  MinDistance n a b c
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b c : Int) (result : Int) (h_precond : solve_precond n a b c) : Prop :=
  result ≥ 0 ∧ (n = 1 → result = 0) ∧ result ≤ (n - 1) * myMax a (myMax b c) ∧ result = MinDistance n a b c

theorem solve_spec_satisfied (n a b c : Int) (h_precond : solve_precond n a b c) :
    solve_postcond n a b c (solve n a b c h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · exact MinDistance_nonneg n a b c h_precond
  · constructor
    · intro h_n_eq_1
      rw [MinDistance, h_n_eq_1]
      simp
    · constructor
      · rw [MinDistance]
        rcases h_precond with ⟨h_n_ge_1, _, _, _, _, _, _, _⟩
        split_ifs with h_n_eq_1
        · simp [h_n_eq_1]
        · apply mul_le_mul_of_nonneg_left
          · apply myMin_le_myMax
          · linarith [h_n_ge_1]
      · rfl
-- </vc-theorems>
