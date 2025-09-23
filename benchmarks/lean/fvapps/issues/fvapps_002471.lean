-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | (h::t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_word_occurrences (words : List String) : WordCountResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_word_occurrences_empty_input :
  count_word_occurrences [] = ⟨0, []⟩ :=
sorry
-- </vc-theorems>