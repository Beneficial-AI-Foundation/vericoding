-- <vc-preamble>
@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

theorem reverseWords_spec_satisfied (words_str: String) (h_precond : reverseWords_precond (words_str)) :
    reverseWords_postcond (words_str) (reverseWords (words_str) h_precond) h_precond := by
  sorry
-- </vc-theorems>