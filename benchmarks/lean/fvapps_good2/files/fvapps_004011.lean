-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlpha (c : Char) : Bool :=
  sorry

def reverse_letter (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_letter_only_letters (s : String) :
  ∀ (c : Char), c ∈ (reverse_letter s).data → isAlpha c := by
  sorry

theorem reverse_letter_length (s : String) :
  (reverse_letter s).length = (s.toList.filter isAlpha).length := by
  sorry

theorem reverse_letter_idempotent (s : String) :
  reverse_letter (reverse_letter s) = String.mk (s.toList.filter isAlpha) := by
  sorry

theorem reverse_letter_preserves_case (s : String) :
  ∃ (perm : List Char → List Char),
    (reverse_letter s).data.map Char.toLower =
    (String.mk (s.toList.filter isAlpha)).data.map Char.toLower := by
  sorry

theorem reverse_letter_empty_no_letters (s : String) :
  (∀ c ∈ s.data, ¬isAlpha c) →
  reverse_letter s = "" := by
  sorry
-- </vc-theorems>