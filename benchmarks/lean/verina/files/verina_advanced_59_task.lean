-- <vc-preamble>
@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Prop :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse

if result then
  forward = backward
else
  forward ≠ backward

theorem palindromeIgnoreNonAlnum_spec_satisfied (s: String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    palindromeIgnoreNonAlnum_postcond (s) (palindromeIgnoreNonAlnum (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>