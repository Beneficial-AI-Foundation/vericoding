-- <vc-preamble>
noncomputable axiom FindSpaceHelper : String → Nat → Int
noncomputable axiom StringToIntHelper : String → Nat → Nat → Int

def TrimNewlines (s : String) : String :=
  if s.length = 0 then s
  else if s.get! ⟨s.length - 1⟩ = '\n' then TrimNewlines (s.take (s.length - 1))
  else s
termination_by s.length
decreasing_by sorry

noncomputable def FindSpace (s : String) : Int :=
  FindSpaceHelper s 0

noncomputable def StringToInt (s : String) : Int :=
  if s.length = 0 then 0
  else if s.get! ⟨0⟩ = '-' ∧ s.length > 1 then
    -(StringToIntHelper (s.drop 1) 0 0)
  else
    StringToIntHelper s 0 0

def IsValidInteger (s : String) : Prop :=
  if s.length = 0 then False
  else if s.get! ⟨0⟩ = '-' then
    s.length > 1 ∧ ∀ i : Nat, 1 ≤ i ∧ i < s.length → '0' ≤ s.get! ⟨i⟩ ∧ s.get! ⟨i⟩ ≤ '9'
  else
    ∀ i : Nat, 0 ≤ i ∧ i < s.length → '0' ≤ s.get! ⟨i⟩ ∧ s.get! ⟨i⟩ ≤ '9'

noncomputable def ValidInputFormat (input : String) : Prop :=
  let trimmed := TrimNewlines input
  let spaceIndex := FindSpace trimmed
  spaceIndex ≥ 0 ∧ spaceIndex < Int.ofNat trimmed.length - 1 ∧
  (spaceIndex ≥ 0 → IsValidInteger (trimmed.take spaceIndex.natAbs)) ∧
  (spaceIndex ≥ 0 → IsValidInteger (trimmed.drop (spaceIndex.natAbs + 1)))

noncomputable def ValidInput (input : String) (S W : Int) : Prop :=
  ValidInputFormat input ∧
  let trimmed := TrimNewlines input
  let spaceIndex := FindSpace trimmed
  (spaceIndex ≥ 0 → 
    let sStr := trimmed.take spaceIndex.natAbs
    let wStr := trimmed.drop (spaceIndex.natAbs + 1)
    StringToInt sStr = S ∧ StringToInt wStr = W)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  (result = "safe\n" ∨ result = "unsafe\n" ∨ result = "") ∧
  (ValidInputFormat input →
    let trimmed := TrimNewlines input
    let spaceIndex := FindSpace trimmed
    (spaceIndex ≥ 0 →
      let S := StringToInt (trimmed.take spaceIndex.natAbs)
      let W := StringToInt (trimmed.drop (spaceIndex.natAbs + 1))
      (W < S → result = "safe\n") ∧ (W ≥ S → result = "unsafe\n"))) ∧
  (¬ValidInputFormat input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
