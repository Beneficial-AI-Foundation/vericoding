-- <vc-preamble>
partial def CountSubstring (s : String) (pattern : String) : Nat :=
  if pattern.length = 0 ∨ s.length < pattern.length then 0
  else if s.take pattern.length = pattern then 1 + CountSubstring (s.drop 1) pattern
  else CountSubstring (s.drop 1) pattern

partial def FindIndex (s : String) (pattern : String) : Int :=
  if pattern.length = 0 ∨ s.length < pattern.length then -1
  else if s.take pattern.length = pattern then 0
  else 
    let rest := FindIndex (s.drop 1) pattern
    if rest = -1 then -1 else 1 + rest

def HasNonOverlappingABAndBA (s : String) : Prop :=
  let abIndex := FindIndex s "AB"
  let baIndex := FindIndex s "BA"
  (abIndex ≥ 0 ∧ baIndex ≥ 0) ∧
  ((abIndex ≥ 0 ∧ abIndex + 2 < s.length ∧ CountSubstring (s.drop (Int.natAbs (abIndex + 2))) "BA" > 0) ∨
   (baIndex ≥ 0 ∧ baIndex + 2 < s.length ∧ CountSubstring (s.drop (Int.natAbs (baIndex + 2))) "AB" > 0))

def ValidInput (input : String) : Prop :=
  input.length ≥ 0

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
  let s := if input.length > 0 ∧ input.back = '\n' then input.dropRight 1 else input
  (result = "YES" ↔ HasNonOverlappingABAndBA s) ∧
  (result = "YES" ∨ result = "NO") ∧
  ((CountSubstring s "AB" = 0 ∨ CountSubstring s "BA" = 0) → result = "NO") ∧
  (let abIndex := FindIndex s "AB"
   let baIndex := FindIndex s "BA"
   (CountSubstring s "AB" > 0 ∧ CountSubstring s "BA" > 0 ∧
    ¬((abIndex ≥ 0 ∧ abIndex + 2 < s.length ∧ CountSubstring (s.drop (Int.natAbs (abIndex + 2))) "BA" > 0) ∨
      (baIndex ≥ 0 ∧ baIndex + 2 < s.length ∧ CountSubstring (s.drop (Int.natAbs (baIndex + 2))) "AB" > 0))) → result = "NO")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>