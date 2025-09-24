-- <vc-preamble>
def ValidInput (s : List Char) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s[i]! = 'a' ∨ s[i]! = 'b'

def MergeConsecutive : List Char → List Char
  | [] => []
  | [x] => [x]
  | x :: y :: xs => 
    if x = y then MergeConsecutive (y :: xs)
    else x :: MergeConsecutive (y :: xs)

def IsPalindrome (s : List Char) : Bool :=
  s = s.reverse

def IsGoodSubstring (s : List Char) (i j : Int) : Prop :=
  ValidInput s ∧ 0 ≤ i ∧ i ≤ j ∧ j < s.length ∧
  let sub := s.drop i.natAbs |>.take (j + 1 - i).natAbs
  IsPalindrome (MergeConsecutive sub)

def ValidOutput (s : List Char) (evenCount oddCount : Int) : Prop :=
  ValidInput s ∧
  evenCount ≥ 0 ∧ oddCount ≥ 0 ∧
  evenCount + oddCount ≥ s.length ∧
  oddCount ≥ s.length ∧
  (s.length = 1 → evenCount = 0 ∧ oddCount = 1)

@[reducible, simp]
def solve_precond (s : List Char) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : List Char) (h_precond : solve_precond s) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : List Char) (result : Int × Int) (h_precond : solve_precond s) : Prop :=
  ValidOutput s result.1 result.2

theorem solve_spec_satisfied (s : List Char) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>