-- <vc-preamble>
def CountOccurrences (s : List Int) (x : Int) : Int :=
  match s with
  | [] => 0
  | h :: t => (if h = x then 1 else 0) + CountOccurrences t x

def FilterPositive (s : List Int) : List Int :=
  match s with
  | [] => []
  | h :: t => if h > 0 then h :: FilterPositive t else FilterPositive t

def RemoveAllOccurrences (s : List Int) (x : Int) : List Int :=
  match s with
  | [] => []
  | h :: t => if h = x then RemoveAllOccurrences t x else h :: RemoveAllOccurrences t x

def CountPairsHelper : List Int → Int
  | [] => 0
  | [_] => 0
  | h :: t =>
    let count := CountOccurrences (h :: t) h
    let remaining := RemoveAllOccurrences (h :: t) h
    (if count = 2 then 1 else 0) + CountPairsHelper remaining
  decreasing_by simp_wf; sorry

def CountPairs (s : List Int) : Int :=
  let positive_sessions := FilterPositive s
  CountPairsHelper positive_sessions

def ExistsIndex (s : List Int) (x : Int) : Prop :=
  ∃ i, 0 ≤ i ∧ i < s.length ∧ s[i]! = x

@[reducible, simp]
def solve_precond (n : Int) (sessions : List Int) : Prop :=
  n ≥ 1 ∧ sessions.length = n ∧ ∀ i, 0 ≤ i ∧ i < sessions.length → sessions[i]! ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (sessions : List Int) (h_precond : solve_precond n sessions) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (sessions : List Int) (result : Int) (h_precond : solve_precond n sessions) : Prop :=
  (result = -1 ∨ result ≥ 0) ∧
  (result = -1 → ∃ id, id > 0 ∧ CountOccurrences sessions id > 2) ∧
  (result ≥ 0 → ∀ id, id > 0 → CountOccurrences sessions id ≤ 2) ∧
  (result ≥ 0 → result = CountPairs sessions)

theorem solve_spec_satisfied (n : Int) (sessions : List Int) (h_precond : solve_precond n sessions) :
    solve_postcond n sessions (solve n sessions h_precond) h_precond := by
  sorry
-- </vc-theorems>