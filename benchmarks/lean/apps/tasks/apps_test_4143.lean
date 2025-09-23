-- <vc-preamble>

def ValidInput (N A B C D E : Int) : Prop :=
  N ≥ 1 ∧ A ≥ 1 ∧ B ≥ 1 ∧ C ≥ 1 ∧ D ≥ 1 ∧ E ≥ 1

def MinCapacity (A B C D E : Int) : Int :=
  let temp1 := if A ≤ B then A else B
  let temp2 := if temp1 ≤ C then temp1 else C
  let temp3 := if temp2 ≤ D then temp2 else D
  if temp3 ≤ E then temp3 else E

def CeilDiv (a b : Int) : Int :=
  (a + b - 1) / b

def CorrectResult (N A B C D E result : Int) : Prop :=
  let minCap := MinCapacity A B C D E
  let groups := CeilDiv N minCap
  result = 4 + groups

@[reducible, simp]
def solve_precond (N A B C D E : Int) : Prop :=
  ValidInput N A B C D E
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N A B C D E : Int) (h_precond : solve_precond N A B C D E) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N A B C D E : Int) (result : Int) (h_precond : solve_precond N A B C D E) : Prop :=
  CorrectResult N A B C D E result ∧ result ≥ 5

theorem solve_spec_satisfied (N A B C D E : Int) (h_precond : solve_precond N A B C D E) :
    solve_postcond N A B C D E (solve N A B C D E h_precond) h_precond := by
  sorry
-- </vc-theorems>