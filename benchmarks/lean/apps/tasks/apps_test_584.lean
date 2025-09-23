-- <vc-preamble>
def IsLetter (c : Char) : Bool :=
  ('a' ≤ c ∧ c ≤ 'z') || ('A' ≤ c ∧ c ≤ 'Z')

def FindNewlineHelper (input : String) (pos : Nat) : Nat :=
  if h : pos ≥ input.length then pos
  else if input.data[pos]! == '\n' then pos
  else FindNewlineHelper input (pos + 1)

def FindNewline (input : String) : Nat :=
  FindNewlineHelper input 0

def IsValidParenthesesSequence (s : String) (pos : Nat) (balance : Int) : Bool :=
  if h : pos ≥ s.length then balance == 0
  else
    let c := s.data[pos]!
    let newBalance := if c == '(' then balance + 1 
                     else if c == ')' then balance - 1 
                     else balance
    newBalance ≥ 0 && IsValidParenthesesSequence s (pos + 1) newBalance

def ValidParentheses (input : String) : Bool :=
  let newlinePos := FindNewline input
  if newlinePos ≥ input.length then true
  else
    let s := if newlinePos + 1 < input.length then input.drop (newlinePos + 1) else ""
    IsValidParenthesesSequence s 0 0

def ComputeLongestOutside (s : String) (pos : Nat) (balance : Int) (cur : Nat) (best : Nat) : Nat :=
  if h : pos ≥ s.length then
    if cur > best && balance == 0 then cur else best
  else
    let c := s.data[pos]!
    let newBalance := if c == '(' then balance + 1 
                     else if c == ')' then (if balance > 0 then balance - 1 else 0)
                     else balance
    let newCur := if IsLetter c then cur + 1
                 else if cur > 0 then 0
                 else cur
    let newBest := if !IsLetter c && cur > 0 && balance == 0 then
                      if cur > best then cur else best
                  else best
    ComputeLongestOutside s (pos + 1) newBalance newCur newBest

def LongestWordOutside (input : String) : Nat :=
  let newlinePos := FindNewline input
  if newlinePos ≥ input.length then 0
  else
    let s := if newlinePos + 1 < input.length then input.drop (newlinePos + 1) else ""
    ComputeLongestOutside s 0 0 0 0

def ComputeCountInside (s : String) (pos : Nat) (balance : Int) (cur : Nat) : Nat :=
  if h : pos ≥ s.length then 0
  else
    let c := s.data[pos]!
    let newBalance := if c == '(' then balance + 1 
                     else if c == ')' then (if balance > 0 then balance - 1 else 0)
                     else balance
    let newCur := if IsLetter c then cur + 1
                 else if cur > 0 then 0
                 else cur
    let wordEnded := !IsLetter c && cur > 0
    let countIncrement := if wordEnded && balance > 0 then 1 else 0
    countIncrement + ComputeCountInside s (pos + 1) newBalance newCur

def CountWordsInside (input : String) : Nat :=
  let newlinePos := FindNewline input
  if newlinePos ≥ input.length then 0
  else
    let s := if newlinePos + 1 < input.length then input.drop (newlinePos + 1) else ""
    ComputeCountInside s 0 0 0

def ValidOutput (input : String) (len_out : Nat) (count_in : Nat) : Bool :=
  len_out == LongestWordOutside input &&
  count_in == CountWordsInside input

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i, i < input.length ∧ input.data[i]! == '\n') ∧
  (∀ i, i < input.length → 
    (IsLetter (input.data[i]!) ∨ input.data[i]! == '_' ∨ 
     input.data[i]! == '(' ∨ input.data[i]! == ')' ∨ 
     input.data[i]! == '\n' ∨ input.data[i]! == '\r' ∨ 
     ('0' ≤ input.data[i]! ∧ input.data[i]! ≤ '9'))) ∧
  ValidParentheses input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : Nat × Nat) (h_precond : solve_precond input) : Prop :=
  result.1 = LongestWordOutside input ∧
  result.2 = CountWordsInside input ∧
  ValidOutput input result.1 result.2

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>