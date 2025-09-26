-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) (s f : Int) : Prop :=
  n ≥ 2 ∧ a.length = n ∧ s ≥ 1 ∧ f > s ∧ f ≤ n ∧
  ∀ i, 0 ≤ i ∧ i < n → a[i.natAbs]! ≥ 1

def participantCountHelper (a : List Int) (s f n start i : Int) : Int :=
  if h : i ≥ n then 0
  else
    let localHour := (start + i - 1) % n + 1
    let contribution := if s ≤ localHour ∧ localHour < f then a[i.natAbs]! else 0
    contribution + participantCountHelper a s f n start (i + 1)
termination_by (n - i).natAbs
decreasing_by
  simp_wf
  have h1 : i < n := Int.not_le.mp h
  omega

def participantCount (a : List Int) (s f n start : Int) : Int :=
  participantCountHelper a s f n start 0

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) (s f : Int) : Prop :=
  ValidInput n a s f
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (s f : Int) (h_precond : solve_precond n a s f) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (s f : Int) (result : Int) (_ : solve_precond n a s f) : Prop :=
  1 ≤ result ∧ result ≤ n ∧
  (∀ start, 1 ≤ start ∧ start ≤ n → 
    participantCount a s f n result ≥ participantCount a s f n start) ∧
  (∀ start, 1 ≤ start ∧ start ≤ n ∧ 
    participantCount a s f n start = participantCount a s f n result 
    → result ≤ start)

theorem solve_spec_satisfied (n : Int) (a : List Int) (s f : Int) (h_precond : solve_precond n a s f) :
    solve_postcond n a s f (solve n a s f h_precond) h_precond := by
  sorry
-- </vc-theorems>