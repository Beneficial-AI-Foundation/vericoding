-- <vc-preamble>
def countVVPairsBefore (s : String) (pos : Nat) : Nat :=
  if pos ≤ 1 then 0
  else
    let prev := countVVPairsBefore s (pos - 1)
    if (pos ≥ 2) && s.data[pos - 1]! == 'v' && s.data[pos - 2]! == 'v' then prev + 1 else prev
termination_by pos

def countVVPairsAfter (s : String) (pos : Nat) : Nat :=
  if pos ≥ s.length - 1 then 0
  else
    let rest := countVVPairsAfter s (pos + 1)
    if pos + 1 < s.length && s.data[pos]! == 'v' && s.data[pos + 1]! == 'v' then rest + 1 else rest
termination_by s.length - pos

def wowFactorSum (s : String) (pos : Nat) : Nat :=
  if pos ≥ s.length then 0
  else
    let current := if s.data[pos]! == 'o' then 
        countVVPairsBefore s pos * countVVPairsAfter s (pos + 1)
    else 0
    current + wowFactorSum s (pos + 1)
termination_by s.length - pos

def wowFactor (s : String) : Nat :=
  if s.length < 4 then 0
  else wowFactorSum s 0

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, i < s.length → s.data[i]! == 'v' ∨ s.data[i]! == 'o'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  Int.ofNat (wowFactor s)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  result ≥ 0 ∧ result = Int.ofNat (wowFactor s)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>