-- <vc-preamble>
def ValidInput (S : String) : Prop :=
  S.length ≥ 3 ∧ ∀ i, 0 ≤ i ∧ i < S.length → '1' ≤ S.data[i]! ∧ S.data[i]! ≤ '9'

def StringToInt (s : String) : Int :=
  if s.length = 3 then
    100 * (s.data[0]!).toNat - 100 * '0'.toNat + 
    10 * (s.data[1]!).toNat - 10 * '0'.toNat + 
    (s.data[2]!).toNat - '0'.toNat
  else 0

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def substring (s : String) (start : Nat) (len : Nat) : String :=
  (s.data.drop start |>.take len).asString

def IsMinimumDifference (S : String) (result : Int) : Prop :=
  ValidInput S →
  result ≥ 0 ∧
  (∃ i, 0 ≤ i ∧ i ≤ S.length - 3 ∧ result = abs (753 - StringToInt (substring S i 3))) ∧
  (∀ i, 0 ≤ i ∧ i ≤ S.length - 3 → result ≤ abs (753 - StringToInt (substring S i 3)))

@[reducible, simp]
def solve_precond (S : String) : Prop :=
  ValidInput S
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
  IsMinimumDifference S result

theorem solve_spec_satisfied (S : String) (h_precond : solve_precond S) :
    solve_postcond S (solve S h_precond) h_precond := by
  sorry
-- </vc-theorems>