-- <vc-preamble>
def CountOccurrences : List Int → Int → Int
  | [], _ => 0
  | x :: xs, target => if x = target then 1 + CountOccurrences xs target else CountOccurrences xs target

def ListSum : List Int → Int
  | [] => 0
  | x :: xs => x + ListSum xs

def ValidInput (n : Int) (ratings : List Int) : Prop :=
  n ≥ 2 ∧ ratings.length = Int.natAbs n

def AllInfected (k : Int) (ratings : List Int) : Prop :=
  k ∈ ratings ∧ CountOccurrences ratings k = ratings.length

def CanInfectInOneContest (k : Int) (ratings : List Int) : Prop :=
  (k ∈ ratings ∧ CountOccurrences ratings k ≠ ratings.length) ∨
  (k ∉ ratings ∧ k * (ratings.length : Int) = ListSum ratings)

def RequiresTwoContests (k : Int) (ratings : List Int) : Prop :=
  k ∉ ratings ∧ k * (ratings.length : Int) ≠ ListSum ratings

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (ratings : List Int) : Prop :=
  ValidInput n ratings
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (ratings : List Int) (h_precond : solve_precond n k ratings) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (ratings : List Int) (result : Int) (h_precond : solve_precond n k ratings) : Prop :=
  result ≥ 0 ∧ result ≤ 2 ∧
  (AllInfected k ratings → result = 0) ∧
  (CanInfectInOneContest k ratings ∧ ¬AllInfected k ratings → result = 1) ∧
  (RequiresTwoContests k ratings → result = 2)

theorem solve_spec_satisfied (n : Int) (k : Int) (ratings : List Int) (h_precond : solve_precond n k ratings) :
    solve_postcond n k ratings (solve n k ratings h_precond) h_precond := by
  sorry
-- </vc-theorems>