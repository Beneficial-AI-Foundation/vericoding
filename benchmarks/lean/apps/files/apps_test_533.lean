-- <vc-preamble>
def ValidInput (a1 a2 k1 k2 n : Int) : Prop :=
  a1 ≥ 1 ∧ a2 ≥ 1 ∧ k1 ≥ 1 ∧ k2 ≥ 1 ∧ n ≥ 1

def MinimumSentOff (a1 a2 k1 k2 n : Int) (h : ValidInput a1 a2 k1 k2 n) : Int :=
  let max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2
  if n - max_non_sendoff_cards > 0 then n - max_non_sendoff_cards else 0

def MaximumSentOff (a1 a2 k1 k2 n : Int) (h : ValidInput a1 a2 k1 k2 n) : Int :=
  if k1 < k2 then
    let team1_sent := if n / k1 < a1 then n / k1 else a1
    let remaining_cards := n - team1_sent * k1
    team1_sent + remaining_cards / k2
  else
    let team2_sent := if n / k2 < a2 then n / k2 else a2
    let remaining_cards := n - team2_sent * k2
    team2_sent + remaining_cards / k1

def ValidResult (a1 a2 k1 k2 n minimum maximum : Int) (h : ValidInput a1 a2 k1 k2 n) : Prop :=
  minimum ≥ 0 ∧ maximum ≥ 0 ∧
  minimum ≤ maximum ∧
  maximum ≤ a1 + a2 ∧
  minimum ≤ n ∧
  maximum ≤ n ∧
  minimum = MinimumSentOff a1 a2 k1 k2 n h ∧
  maximum = MaximumSentOff a1 a2 k1 k2 n h

@[reducible, simp]
def solve_precond (a1 a2 k1 k2 n : Int) : Prop :=
  ValidInput a1 a2 k1 k2 n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a1 a2 k1 k2 n : Int) (h_precond : solve_precond a1 a2 k1 k2 n) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a1 a2 k1 k2 n : Int) (result: Int × Int) (h_precond : solve_precond a1 a2 k1 k2 n) : Prop :=
  ValidResult a1 a2 k1 k2 n result.1 result.2 h_precond

theorem solve_spec_satisfied (a1 a2 k1 k2 n : Int) (h_precond : solve_precond a1 a2 k1 k2 n) :
    solve_postcond a1 a2 k1 k2 n (solve a1 a2 k1 k2 n h_precond) h_precond := by
  sorry
-- </vc-theorems>