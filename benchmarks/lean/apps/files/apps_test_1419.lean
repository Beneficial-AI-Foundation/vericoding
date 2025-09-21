-- <vc-preamble>
axiom checkFormatting : String → Int → Int → Nat → Int → Int → Prop

def canFormatText (s : String) (k : Int) (maxWidth : Int) : Prop :=
  k ≥ 1 ∧ s.length ≥ 1 ∧ maxWidth ≥ 1 ∧ checkFormatting s k maxWidth 0 1 0

@[reducible, simp]
def solve_precond (k : Int) (s : String) : Prop :=
  k ≥ 1 ∧ s.length ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k : Int) (s : String) (h_precond : solve_precond k s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k : Int) (s : String) (result : Int) (h_precond : solve_precond k s) : Prop :=
  result ≥ 1 ∧ 
  result ≤ s.length ∧ 
  canFormatText s k result ∧ 
  (result > 1 → ¬canFormatText s k (result - 1))

theorem solve_spec_satisfied (k : Int) (s : String) (h_precond : solve_precond k s) :
    solve_postcond k s (solve k s h_precond) h_precond := by
  sorry
-- </vc-theorems>