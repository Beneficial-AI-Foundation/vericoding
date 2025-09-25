-- <vc-preamble>
def IsValidString (s : String) : Prop :=
  s.length > 0

def IsValidProblemString (s : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = '>' ∨ s.data[i]! = '<'

def IsValidIntegerString (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def StringToIntHelper (s : String) (pos : Nat) : Int :=
  if pos = 0 then 0
  else StringToIntHelper s (pos - 1) * 10 + (s.data[pos - 1]!.toNat - '0'.toNat)

def StringToInt (s : String) : Int :=
  StringToIntHelper s s.length

def FirstGreaterFromLeftHelper (s : String) (pos : Nat) : Nat :=
  if pos ≥ s.length then s.length
  else if s.data[pos]! = '>' then pos
  else FirstGreaterFromLeftHelper s (pos + 1)
termination_by s.length - pos

def FirstGreaterFromLeft (s : String) : Nat :=
  FirstGreaterFromLeftHelper s 0

def FirstLessFromRightHelper (s : String) (pos : Nat) : Nat :=
  if pos = 0 then s.length
  else if s.data[pos - 1]! = '<' then s.length - pos
  else FirstLessFromRightHelper s (pos - 1)
termination_by pos

def FirstLessFromRight (s : String) : Nat :=
  if s.length = 0 then 0
  else FirstLessFromRightHelper s s.length

def MinDeletionsNeeded (s : String) : Nat :=
  let firstGreater := FirstGreaterFromLeft s
  let firstLessFromRight := FirstLessFromRight s
  if firstGreater < firstLessFromRight then firstGreater else firstLessFromRight

def min (a b : Int) : Int :=
  if a < b then a else b

@[reducible, simp]
def solve_precond (lines : List String) : Prop :=
  lines.length > 0 ∧
  (∀ i, 0 ≤ i ∧ i < lines.length → IsValidString lines[i]!) ∧
  IsValidIntegerString lines[0]! ∧
  (let t := StringToInt lines[0]!;
   lines.length ≥ 1 + 2 * t.natAbs) ∧
  (let t := StringToInt lines[0]!;
   ∀ i, 0 ≤ i ∧ i < t →
     IsValidIntegerString lines[1 + 2*i.natAbs]! ∧
     IsValidProblemString lines[2 + 2*i.natAbs]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (lines : List String) (h_precond : solve_precond lines) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (lines : List String) (results : List Int) (h_precond : solve_precond lines) : Prop :=
  let t := StringToInt lines[0]!;
  results.length = t.natAbs ∧
  (∀ r, r ∈ results → r ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < results.length →
    results[i]! = MinDeletionsNeeded lines[2 + 2*i]!)

theorem solve_spec_satisfied (lines : List String) (h_precond : solve_precond lines) :
    solve_postcond lines (solve lines h_precond) h_precond := by
  sorry
-- </vc-theorems>