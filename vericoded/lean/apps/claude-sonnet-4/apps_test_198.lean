import Mathlib
-- <vc-preamble>
def ValidRectangleParts (a b n : Int) : Prop :=
  a > 0 ∧ b > 0 ∧ a ≠ b ∧ 2 * a + 2 * b = n

def CountValidRectangles (n : Int) : Int :=
  if n % 2 = 1 then 0
  else if n % 4 = 2 then n / 4
  else n / 4 - 1

def ValidInput (n : Int) : Prop :=
  n > 0

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: lemmas for modular arithmetic
lemma mod_two_cases (n : Int) : n % 2 = 0 ∨ n % 2 = 1 := by
  exact Int.emod_two_eq_zero_or_one n

lemma mod_four_cases (n : Int) (h : n % 2 = 0) : n % 4 = 0 ∨ n % 4 = 2 := by
  have h_range : 0 ≤ n % 4 ∧ n % 4 < 4 := by
    constructor
    · exact Int.emod_nonneg n (by norm_num)
    · exact Int.emod_lt_of_pos n (by norm_num)
  -- Since n % 4 ∈ {0, 1, 2, 3} and n is even, n % 4 must be even
  -- So n % 4 ∈ {0, 2}
  have h_four_vals : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  cases h_four_vals with
  | inl h0 => left; exact h0
  | inr h_rest => 
    cases h_rest with
    | inl h1 => 
      -- n % 4 = 1 implies n is odd, contradicting h
      exfalso
      have : n % 2 = (n % 4) % 2 := by rw [Int.emod_emod_of_dvd]; norm_num
      rw [h1] at this
      rw [this] at h
      norm_num at h
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h2 => right; exact h2
      | inr h3 =>
        -- n % 4 = 3 implies n is odd, contradicting h
        exfalso
        have : n % 2 = (n % 4) % 2 := by rw [Int.emod_emod_of_dvd]; norm_num
        rw [h3] at this
        rw [this] at h
        norm_num at h
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  CountValidRectangles n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result = CountValidRectangles n ∧
  (n % 2 = 1 → result = 0) ∧
  (n % 2 = 0 ∧ n % 4 = 2 → result = n / 4) ∧
  (n % 2 = 0 ∧ n % 4 = 0 → result = n / 4 - 1)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve CountValidRectangles
  constructor
  · rfl
  constructor
  · intro h_odd
    simp [h_odd]
  constructor
  · intro ⟨h_even, h_mod4⟩
    simp [h_even, h_mod4]
  · intro ⟨h_even, h_mod4⟩
    simp [h_even, h_mod4]
-- </vc-theorems>
