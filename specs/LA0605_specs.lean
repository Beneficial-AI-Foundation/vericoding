-- <vc-preamble>
def IsEvenString (s : String) : Prop :=
  s.length ≥ 2 ∧ s.length % 2 = 0 ∧ s.take (s.length / 2) = s.drop (s.length / 2)

def ValidInput (S : String) : Prop :=
  S.length ≥ 2 ∧ IsEvenString S

def ValidSolution (S : String) (result : Int) : Prop :=
  2 ≤ result ∧ result < S.length ∧ result % 2 = 0 ∧ IsEvenString (S.take result.natAbs)

def IsMaximalSolution (S : String) (result : Int) : Prop :=
  ValidSolution S result ∧ 
  ∀ k, result < k ∧ k < S.length ∧ k % 2 = 0 → ¬IsEvenString (S.take k.natAbs)

@[reducible, simp]
def solve_precond (S : String) : Prop :=
  ValidInput S ∧ ∃ k, ValidSolution S k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (S : String) (h_precond : solve_precond S) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (S : String) (result : Int) (h_precond : solve_precond S) : Prop :=
  ValidSolution S result ∧ IsMaximalSolution S result

theorem solve_spec_satisfied (S : String) (h_precond : solve_precond S) :
    solve_postcond S (solve S h_precond) h_precond := by
  sorry
-- </vc-theorems>