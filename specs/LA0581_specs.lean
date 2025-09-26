-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 2 ∧
  (∃ i, 0 < i ∧ i < input.length ∧ input.data[i]? = some ' ') ∧
  (∀ i, 0 ≤ i ∧ i < input.length → (input.data[i]? = some ' ' ∨ input.data[i]? = some '\n' ∨ (∃ c, input.data[i]? = some c ∧ 'a' ≤ c ∧ c ≤ 'z'))) ∧
  (∃ i, 0 < i ∧ i < input.length ∧ input.data[i]? = some ' ' ∧ 
   (∀ j, 0 ≤ j ∧ j < i → input.data[j]? ≠ some ' ' ∧ input.data[j]? ≠ some '\n') ∧
   (∀ j, i+1 ≤ j ∧ j < input.length → input.data[j]? ≠ some ' ' ∧ input.data[j]? ≠ some '\n'))

def ValidOutput (output : String) : Prop :=
  output.length > 0 ∧
  output.data[output.length-1]? = some '\n' ∧
  (∀ i, 0 ≤ i ∧ i < output.length-1 → (∃ c, output.data[i]? = some c ∧ 'a' ≤ c ∧ c ≤ 'z'))

def findSpacePos (input : String) : Nat := 0

def ExtractStrings (input : String) : String × String :=
  let spacePos := findSpacePos input
  let s := ⟨input.data.take spacePos⟩
  let t := if input.data[input.length-1]? = some '\n' 
           then ⟨(input.data.drop (spacePos+1)).dropLast⟩
           else ⟨input.data.drop (spacePos+1)⟩
  (s, t)

def CorrectConcatenation (input : String) (output : String) : Prop :=
  let (s, t) := ExtractStrings input
  output = t ++ s ++ "\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result ∧ CorrectConcatenation input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>