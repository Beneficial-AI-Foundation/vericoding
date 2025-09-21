-- <vc-preamble>
def SumSeq (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: t => h + SumSeq t

def ValidInput (n : Int) (d : Int) (t : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ d ∧ d ≤ 10000 ∧
  t.length = n ∧
  ∀ i, 0 ≤ i ∧ i < t.length → 1 ≤ t[i]! ∧ t[i]! ≤ 100

def MinTimeNeeded (n : Int) (t : List Int) : Int :=
  SumSeq t + 10 * (n - 1)

def ValidResult (n : Int) (d : Int) (t : List Int) (result : Int) : Prop :=
  let songSum := SumSeq t
  let minTime := MinTimeNeeded n t
  if minTime > d then
    result = -1
  else
    result = (d - songSum) / 5 ∧ result ≥ 0

@[reducible, simp]
def solve_precond (n : Int) (d : Int) (t : List Int) : Prop :=
  ValidInput n d t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (d : Int) (t : List Int) (h_precond : solve_precond n d t) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (d : Int) (t : List Int) (result : Int) (h_precond : solve_precond n d t) : Prop :=
  ValidResult n d t result

theorem solve_spec_satisfied (n : Int) (d : Int) (t : List Int) (h_precond : solve_precond n d t) :
    solve_postcond n d t (solve n d t h_precond) h_precond := by
  sorry
-- </vc-theorems>