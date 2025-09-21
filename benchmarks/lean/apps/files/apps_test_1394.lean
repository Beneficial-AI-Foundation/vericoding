-- <vc-preamble>
def CountAs (s : String) : Nat := 
  match s with
  | ⟨[]⟩ => 0
  | ⟨c :: cs⟩ => 
      let rest := ⟨cs⟩
      if c = 'a' then 1 + CountAs rest else CountAs rest

def RemoveAs (s : String) : String := 
  match s with
  | ⟨[]⟩ => ""
  | ⟨c :: cs⟩ => 
      let rest := ⟨cs⟩
      if c = 'a' then RemoveAs rest else ⟨[c]⟩ ++ RemoveAs rest

@[reducible, simp]
def solve_precond (t : String) : Prop :=
  t.length ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (t : String) (h_precond : solve_precond t) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t : String) (result : String) (h_precond : solve_precond t) : Prop :=
  (result = ":(" ∨ (result.length ≤ t.length ∧ t = result ++ RemoveAs result)) ∧
  (result ≠ ":(" → (
    let z := CountAs t
    let nonACount := t.length - z
    nonACount % 2 = 0 ∧
    let q := nonACount / 2
    let sLength := q + z
    sLength ≤ t.length ∧
    result = t.take sLength ∧
    RemoveAs result = t.drop sLength
  ))

theorem solve_spec_satisfied (t : String) (h_precond : solve_precond t) :
    solve_postcond t (solve t h_precond) h_precond := by
  sorry
-- </vc-theorems>