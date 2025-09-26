-- <vc-preamble>
def CountCharacter (s : List Char) (c : Char) : Nat :=
  match s with
  | [] => 0
  | h :: t => (if h = c then 1 else 0) + CountCharacter t c

def HasSameCharacterCounts (s t : List Char) : Prop :=
  s.length = t.length ∧ 
  (∀ c, CountCharacter s c = CountCharacter t c)

def FindNextMatch (s : List Char) (c : Char) (start : Nat) : Nat :=
  if start ≥ s.length then s.length
  else if s[start]! = c then start
  else FindNextMatch s c (start + 1)
termination_by s.length - start

def CanMatchSubstring (s t : List Char) (i j k : Nat) : Bool :=
  if i > j then true
  else if k ≥ s.length then false
  else 
    let nextK := FindNextMatch s t[j]! k
    if nextK ≥ s.length then false
    else if i = j then true
    else CanMatchSubstring s t i (j-1) (nextK+1)
termination_by j + 1 - i

partial def MaxPreservableLength (s t : List Char) (i j maxSoFar : Nat) : Nat :=
  if i ≥ t.length then maxSoFar
  else if j ≥ t.length then MaxPreservableLength s t (i+1) (i+1) maxSoFar
  else 
    let currentLen := j - i + 1
    let canMatch := CanMatchSubstring s t i j 0
    let newMax := if canMatch && currentLen > maxSoFar then currentLen else maxSoFar
    MaxPreservableLength s t i (j+1) newMax

def MaxLongestSubsequence (s t : List Char) : Nat :=
  if s.length = 0 then 0
  else MaxPreservableLength s t 0 0 0

@[reducible, simp]
def solve_precond (s t : List Char) : Prop :=
  s.length = t.length ∧ s.length ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s t : List Char) (h_precond : solve_precond s t) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s t : List Char) (result : Int) (h_precond : solve_precond s t) : Prop :=
  (result = -1 ↔ ¬HasSameCharacterCounts s t) ∧
  result ≥ -1 ∧
  (result ≠ -1 → 0 ≤ result ∧ result ≤ s.length) ∧
  (result ≠ -1 → HasSameCharacterCounts s t) ∧
  (result ≠ -1 → result = s.length - MaxLongestSubsequence s t) ∧
  (s.length = 0 → result = 0)

theorem solve_spec_satisfied (s t : List Char) (h_precond : solve_precond s t) :
    solve_postcond s t (solve s t h_precond) h_precond := by
  sorry
-- </vc-theorems>