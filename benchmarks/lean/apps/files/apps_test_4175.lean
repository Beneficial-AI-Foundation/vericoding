-- <vc-preamble>
def NoRepeats (words : List String) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < words.length → words[i]! ≠ words[j]!

def ConsecutiveCharsMatch (words : List String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < words.length - 1 → 
    words[i]!.data[words[i]!.length - 1]! = words[i+1]!.data[0]!

def ValidShiritori (words : List String) : Prop :=
  NoRepeats words ∧ ConsecutiveCharsMatch words

@[reducible, simp]
def solve_precond (words : List String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < words.length → words[i]!.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (words : List String) (h_precond : solve_precond words) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (words : List String) (result : String) (h_precond : solve_precond words) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ ValidShiritori words)

theorem solve_spec_satisfied (words : List String) (h_precond : solve_precond words) :
    solve_postcond words (solve words h_precond) h_precond := by
  sorry
-- </vc-theorems>