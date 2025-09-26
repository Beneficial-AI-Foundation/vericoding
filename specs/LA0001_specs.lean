-- <vc-preamble>
def ValidInput (n pos l r : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ pos ∧ pos ≤ n ∧ 1 ≤ l ∧ l ≤ r ∧ r ≤ n

def NoTabsToClose (l r n : Int) : Prop :=
  l = 1 ∧ r = n

def OnlyCloseRight (l r n : Int) : Prop :=
  l = 1 ∧ r < n

def OnlyCloseLeft (l r n : Int) : Prop :=
  l > 1 ∧ r = n

def CloseBothSides (l r n : Int) : Prop :=
  l > 1 ∧ r < n

@[reducible, simp]
def solve_precond (n pos l r : Int) : Prop :=
  ValidInput n pos l r
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n pos l r : Int) (h_precond : solve_precond n pos l r) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n pos l r : Int) (result : Int) (h_precond : solve_precond n pos l r) : Prop :=
  result ≥ 0 ∧
  (NoTabsToClose l r n → result = 0) ∧
  (OnlyCloseRight l r n → result = Int.natAbs (pos - r) + 1) ∧
  (OnlyCloseLeft l r n → result = Int.natAbs (pos - l) + 1) ∧
  (CloseBothSides l r n ∧ l ≤ pos ∧ pos ≤ r ∧ pos - l < r - pos → result = (pos - l) + 1 + (r - l) + 1) ∧
  (CloseBothSides l r n ∧ l ≤ pos ∧ pos ≤ r ∧ pos - l ≥ r - pos → result = (r - pos) + 1 + (r - l) + 1) ∧
  (CloseBothSides l r n ∧ pos > r → result = (pos - r) + 1 + (r - l) + 1) ∧
  (CloseBothSides l r n ∧ pos < l → result = (l - pos) + 1 + (r - l) + 1) ∧
  result ≤ 2 * n

theorem solve_spec_satisfied (n pos l r : Int) (h_precond : solve_precond n pos l r) :
    solve_postcond n pos l r (solve n pos l r h_precond) h_precond := by
  sorry
-- </vc-theorems>