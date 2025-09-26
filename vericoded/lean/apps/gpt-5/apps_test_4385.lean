import Mathlib
-- <vc-preamble>
def ValidInput (a b c d e k : Int) : Prop :=
  0 ≤ a ∧ a ≤ 123 ∧ 0 ≤ b ∧ b ≤ 123 ∧ 0 ≤ c ∧ c ≤ 123 ∧
  0 ≤ d ∧ d ≤ 123 ∧ 0 ≤ e ∧ e ≤ 123 ∧ 0 ≤ k ∧ k ≤ 123 ∧
  a < b ∧ b < c ∧ c < d ∧ d < e

def AllPairsCanCommunicate (a b c d e k : Int) : Prop :=
  (e - a) ≤ k

@[reducible, simp]
def solve_precond (a b c d e k : Int) : Prop :=
  ValidInput a b c d e k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance instDecidableAllPairsCanCommunicate (a b c d e k : Int) :
    Decidable (AllPairsCanCommunicate a b c d e k) := by
  unfold AllPairsCanCommunicate
  infer_instance

-- LLM HELPER
@[simp] lemma yay_ne_sad : "Yay!" ≠ ":(" := by decide
-- LLM HELPER
@[simp] lemma sad_ne_yay : ":(" ≠ "Yay!" := by decide
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d e k : Int) (h_precond : solve_precond a b c d e k) : String :=
  if AllPairsCanCommunicate a b c d e k then "Yay!" else ":("
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d e k : Int) (result : String) (h_precond : solve_precond a b c d e k) : Prop :=
  (result = "Yay!" ↔ AllPairsCanCommunicate a b c d e k) ∧
  (result = ":(" ↔ ¬AllPairsCanCommunicate a b c d e k)

theorem solve_spec_satisfied (a b c d e k : Int) (h_precond : solve_precond a b c d e k) :
    solve_postcond a b c d e k (solve a b c d e k h_precond) h_precond := by
  classical
by_cases h : AllPairsCanCommunicate a b c d e k
· simp [solve_postcond, solve, h, yay_ne_sad, sad_ne_yay]
· simp [solve_postcond, solve, h, yay_ne_sad, sad_ne_yay]
-- </vc-theorems>
