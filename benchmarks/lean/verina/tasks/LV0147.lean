-- <vc-preamble>
@[reducible, simp]
def IsPalindrome_precond (x : List Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true
-- </vc-helpers>

-- <vc-definitions>
def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)

theorem IsPalindrome_spec_satisfied (x: List Char) (h_precond : IsPalindrome_precond (x)) :
    IsPalindrome_postcond (x) (IsPalindrome (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>