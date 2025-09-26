-- <vc-preamble>
def ValidInput (s : String) (k : Int) : Prop :=
  1 ≤ k ∧ k ≤ 26 ∧ 1 ≤ s.length ∧ s.length ≤ 1000 ∧ 
  ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def UniqueChars (s : String) : Nat :=
  s.data.eraseDups.length

def MinChanges (s : String) (k : Int) : Int :=
  let unique := UniqueChars s
  if k ≤ unique then 0 else k - unique

def IsImpossible (s : String) (k : Int) : Prop :=
  s.length < k

def IntToString (n : Int) : String := toString n

@[reducible, simp]
def solve_precond (s : String) (k : Int) : Prop :=
  ValidInput s k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Int) (h_precond : solve_precond s k) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (k : Int) (result: String) (h_precond : solve_precond s k) : Prop :=
  (IsImpossible s k → result = "impossible") ∧
  (¬IsImpossible s k → result = IntToString (MinChanges s k))

theorem solve_spec_satisfied (s : String) (k : Int) (h_precond : solve_precond s k) :
    solve_postcond s k (solve s k h_precond) h_precond := by
  sorry
-- </vc-theorems>