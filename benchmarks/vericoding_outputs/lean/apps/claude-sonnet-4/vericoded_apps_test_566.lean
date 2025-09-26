import Mathlib
-- <vc-preamble>
def ValidInput (r g b : Int) : Prop :=
  r ≥ 0 ∧ g ≥ 0 ∧ b ≥ 0

def mymin (a b : Int) : Int :=
  if a ≤ b then a else b

def MaxTables (r g b : Int) : Int :=
  mymin (mymin (mymin ((r + g + b) / 3) (r + g)) (r + b)) (g + b)

@[reducible, simp]
def solve_precond (r g b : Int) : Prop :=
  ValidInput r g b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma showing mymin preserves non-negativity
lemma mymin_nonneg (a b : Int) (ha : a ≥ 0) (hb : b ≥ 0) : mymin a b ≥ 0 := by
  unfold mymin
  split_ifs with h
  · exact ha
  · exact hb

-- LLM HELPER: Lemma about mymin and smaller values
lemma mymin_le_left (a b : Int) : mymin a b ≤ a := by
  unfold mymin
  split_ifs with h
  · rfl
  · linarith

lemma mymin_le_right (a b : Int) : mymin a b ≤ b := by
  unfold mymin
  split_ifs with h
  · linarith
  · rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (r g b : Int) (h_precond : solve_precond r g b) : Int :=
  MaxTables r g b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r g b : Int) (result : Int) (h_precond : solve_precond r g b) : Prop :=
  result = MaxTables r g b ∧ result ≥ 0

theorem solve_spec_satisfied (r g b : Int) (h_precond : solve_precond r g b) :
    solve_postcond r g b (solve r g b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · rfl
  · -- Need to show MaxTables r g b ≥ 0
    unfold MaxTables
    have h_valid := h_precond
    simp at h_valid
    obtain ⟨hr, hg, hb⟩ := h_valid
    -- Use the helper lemmas to show the result is non-negative
    apply mymin_nonneg
    · apply mymin_nonneg
      · apply mymin_nonneg
        · -- Show (r + g + b) / 3 ≥ 0
          apply Int.ediv_nonneg
          linarith
          norm_num
        · linarith
      · linarith
    · linarith
-- </vc-theorems>
