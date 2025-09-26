import Mathlib
-- <vc-preamble>
def ValidInput (n x a b : Int) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ 0 ≤ x ∧ x ≤ 100 ∧ 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ a ≠ b

def MaxDistance (n x a b : Int) (h : ValidInput n x a b) : Int :=
  let initialDistance := if a ≥ b then a - b else b - a
  let maxPossibleDistance := initialDistance + x
  let maxLineDistance := n - 1
  if maxPossibleDistance ≤ maxLineDistance then maxPossibleDistance else maxLineDistance

def ValidResult (n x a b result : Int) (h : ValidInput n x a b) : Prop :=
  result = MaxDistance n x a b h ∧ 0 ≤ result ∧ result ≤ n - 1

@[reducible, simp]
def solve_precond (n x a b : Int) : Prop :=
  ValidInput n x a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma maxDistance_bounds (n x a b : Int) (h : ValidInput n x a b) :
    0 ≤ MaxDistance n x a b h ∧ MaxDistance n x a b h ≤ n - 1 := by
  unfold MaxDistance ValidInput at *
  obtain ⟨hn2, hn100, hx0, hx100, ha1, han, hb1, hbn, hab⟩ := h
  simp only [ge_iff_le]
  split_ifs with h1 h2
  · constructor
    · omega
    · omega
  · constructor
    · omega
    · rfl
  · constructor
    · omega
    · omega
  · constructor
    · omega
    · rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n x a b : Int) (h_precond : solve_precond n x a b) : Int :=
  MaxDistance n x a b h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n x a b : Int) (result : Int) (h_precond : solve_precond n x a b) : Prop :=
  ValidResult n x a b result h_precond ∧ result ≥ 0

theorem solve_spec_satisfied (n x a b : Int) (h_precond : solve_precond n x a b) :
    solve_postcond n x a b (solve n x a b h_precond) h_precond := by
  unfold solve_postcond solve ValidResult
  constructor
  · constructor
    · rfl
    · exact maxDistance_bounds n x a b h_precond
  · exact (maxDistance_bounds n x a b h_precond).1
-- </vc-theorems>
