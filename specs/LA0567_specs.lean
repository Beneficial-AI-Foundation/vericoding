-- <vc-preamble>
def ValidInput (a : Array Int) (allowedPos : Array Bool) : Prop :=
  a.size > 1 ∧ allowedPos.size = a.size

def IsSorted (a : Array Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < a.size - 1 → a[i]! ≤ a[i + 1]!

def CanReachConfiguration (original target : List Int) (allowed : List Bool) : Prop :=
  original.length = target.length ∧ target.length = allowed.length ∧
  original.length = target.length

def BubblePassHelper (s : List Int) (pos : Nat) : List Int :=
  if pos ≥ s.length - 1 then s
  else if h : pos < s.length ∧ pos + 1 < s.length then
    if s[pos]! > s[pos + 1]! then
      let swapped := s.set pos s[pos + 1]! |>.set (pos + 1) s[pos]!
      BubblePassHelper swapped (pos + 1)
    else
      BubblePassHelper s (pos + 1)
  else s

def BubblePass (s : List Int) : List Int :=
  if s.length ≤ 1 then s
  else BubblePassHelper s 0

def BubbleSortHelper (s : List Int) (passes : Nat) : List Int :=
  if passes = 0 then s
  else 
    let afterPass := BubblePass s
    BubbleSortHelper afterPass (passes - 1)

def BubbleSortSeq (s : List Int) : List Int :=
  if s.length ≤ 1 then s
  else BubbleSortHelper s s.length

def SortSequence (s : List Int) : List Int :=
  if s.length ≤ 1 then s
  else BubbleSortSeq s

@[reducible, simp]
def solve_precond (a : Array Int) (allowedPos : Array Bool) : Prop :=
  ValidInput a allowedPos
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : Array Int) (allowedPos : Array Bool) (h_precond : solve_precond a allowedPos) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : Array Int) (allowedPos : Array Bool) (result : Bool) (h_precond : solve_precond a allowedPos) (old_a : Array Int) : Prop :=
  a.toList.length = old_a.toList.length ∧ result = IsSorted a

theorem solve_spec_satisfied (a : Array Int) (allowedPos : Array Bool) (h_precond : solve_precond a allowedPos) (old_a : Array Int) :
    solve_postcond a allowedPos (solve a allowedPos h_precond) h_precond old_a := by
  sorry
-- </vc-theorems>