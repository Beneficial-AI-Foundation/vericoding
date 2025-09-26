import Mathlib
-- <vc-preamble>
def Distance (s t : Int) : Nat :=
  if s ≥ t then Int.natAbs (s - t) else Int.natAbs (t - s)

def ValidInput (x a b : Int) : Prop :=
  1 ≤ x ∧ x ≤ 1000 ∧
  1 ≤ a ∧ a ≤ 1000 ∧
  1 ≤ b ∧ b ≤ 1000 ∧
  x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
  Distance x a ≠ Distance x b

def CorrectResult (x a b : Int) (result : String) : Prop :=
  (result = "A" ↔ Distance x a < Distance x b) ∧
  (result = "B" ↔ Distance x b < Distance x a)

@[reducible, simp]
def solve_precond (x a b : Int) : Prop :=
  ValidInput x a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem ValidInput.dist_ne {x a b : Int} (h : ValidInput x a b) :
    Distance x a ≠ Distance x b := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hdist_ne⟩
  exact hdist_ne
-- </vc-helpers>

-- <vc-definitions>
def solve (x a b : Int) (h_precond : solve_precond x a b) : String :=
  if Distance x a < Distance x b then "A" else "B"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x a b : Int) (result : String) (h_precond : solve_precond x a b) : Prop :=
  (result = "A" ∨ result = "B") ∧ CorrectResult x a b result

theorem solve_spec_satisfied (x a b : Int) (h_precond : solve_precond x a b) :
    solve_postcond x a b (solve x a b h_precond) h_precond := by
  unfold solve_postcond
  have hneq : Distance x a ≠ Distance x b := ValidInput.dist_ne h_precond
  by_cases hlt : Distance x a < Distance x b
  · have hresA : solve x a b h_precond = "A" := by simp [solve, hlt]
    refine And.intro ?_ ?_
    · exact Or.inl hresA
    · refine And.intro ?_ ?_
      · apply Iff.intro
        · intro _; exact hlt
        · intro _; simpa [solve, hlt]
      · apply Iff.intro
        · intro hB
          have hABne : "A" ≠ "B" := by decide
          exact (hABne (by simpa [hresA] using hB)).elim
        · intro hb_lt
          exact (lt_asymm hb_lt hlt).elim
  · have hresB : solve x a b h_precond = "B" := by simp [solve, hlt]
    have hle : Distance x b ≤ Distance x a := by
      have : ¬ Distance x b > Distance x a := by
        simpa [gt_iff_lt] using hlt
      exact le_of_not_gt this
    have hlt' : Distance x b < Distance x a :=
      lt_of_le_of_ne hle (Ne.symm hneq)
    refine And.intro ?_ ?_
    · exact Or.inr hresB
    · refine And.intro ?_ ?_
      · apply Iff.intro
        · intro hAres
          have hABne : "A" ≠ "B" := by decide
          exact (hABne (by simpa [hresB] using hAres)).elim
        · intro hltpos
          exact (hlt hltpos).elim
      · apply Iff.intro
        · intro _; exact hlt'
        · intro _; simpa [solve, hlt]
-- </vc-theorems>
