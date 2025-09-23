-- <vc-preamble>
def is_s_palindrome (s : String) : Prop :=
  let pal := ['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y']
  ∀ i : Nat, 0 ≤ i ∧ i < s.length → 
    let j := s.length - 1 - i
    if i ≥ j then True
    else
      let char_i := s.data.get! i
      let char_j := s.data.get! j
      if char_i = char_j then char_i ∈ pal
      else (char_i = 'p' ∧ char_j = 'q') ∨ 
           (char_i = 'q' ∧ char_j = 'p') ∨
           (char_i = 'b' ∧ char_j = 'd') ∨ 
           (char_i = 'd' ∧ char_j = 'b')

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  (result = "TAK" ∨ result = "NIE") ∧ (result = "TAK" ↔ is_s_palindrome s)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>