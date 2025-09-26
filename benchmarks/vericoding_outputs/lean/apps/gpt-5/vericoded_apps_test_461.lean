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
lemma myMin_le_left (x y : Int) : myMin x y ≤ x := by
  dsimp [myMin]
  by_cases h : x ≤ y
  · simp [h]
  ·
    have hyx : y ≤ x := by
      have ht := le_total y x
      cases ht with
      | inl h1 => exact h1
      | inr h2 => exact (False.elim (h h2))
    simp [h, hyx]

-- LLM HELPER
lemma le_myMax_left (x y : Int) : x ≤ myMax x y := by
  dsimp [myMax]
  by_cases h : x ≥ y
  · simp [h]
  ·
    have hxy : x ≤ y := by
      have ht := le_total x y
      cases ht with
      | inl h1 => exact h1
      | inr h2 => exact (False.elim (h h2))
    simp [h, hxy]

-- LLM HELPER
lemma myMin_nonneg_of_nonneg (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ myMin x y := by
  dsimp [myMin]
  by_cases h : x ≤ y
  · simpa [h] using hx
  · simpa [h] using hy
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
  rcases h_precond with ⟨hn1, hn100, ha1, ha100, hb1, hb100, hc1, hc100⟩
  dsimp [solve_postcond, solve]
  constructor
  · -- nonneg
    by_cases h : n = 1
    · simp [MinDistance, h]
    ·
      have hnm1_nonneg : 0 ≤ n - 1 := sub_nonneg.mpr hn1
      have ha0 : 0 ≤ a := le_trans (by decide : (0 : Int) ≤ 1) ha1
      have hb0 : 0 ≤ b := le_trans (by decide : (0 : Int) ≤ 1) hb1
      have hmin0 : 0 ≤ myMin a b := myMin_nonneg_of_nonneg a b ha0 hb0
      have : 0 ≤ (n - 1) * myMin a b := mul_nonneg hnm1_nonneg hmin0
      simpa [MinDistance, h] using this
  constructor
  · intro h; simp [MinDistance, h]
  constructor
  · -- upper bound
    by_cases h : n = 1
    · simp [MinDistance, h]
    ·
      have hnm1_nonneg : 0 ≤ n - 1 := sub_nonneg.mpr hn1
      have h_min_le_max : myMin a b ≤ myMax a (myMax b c) :=
        le_trans (myMin_le_left a b) (le_myMax_left a (myMax b c))
      have h_ineq : (n - 1) * myMin a b ≤ (n - 1) * myMax a (myMax b c) :=
        mul_le_mul_of_nonneg_left h_min_le_max hnm1_nonneg
      simpa [MinDistance, h] using h_ineq
  · rfl
-- </vc-theorems>
