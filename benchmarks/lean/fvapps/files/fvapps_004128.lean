-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def could_be (original : String) (another : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_names (name1 name2 : String) :
  name1.trim ≠ "" → name1 = name2 → could_be name1 name2 := by
  sorry

theorem empty_strings (original another : String) :
  another.trim = "" ∨ original = "" → ¬could_be original another := by
  sorry

theorem subset_match (full_name : String) (partial_name : String) :
  partial_name.trim ≠ "" →
  (∀ word, word ∈ (partial_name.split fun c => c = ' ') →
    word ∈ (full_name.split fun c => c = ' ')) →
  could_be full_name partial_name := by
  sorry

theorem reflexive (name : String) :
  name.trim ≠ "" → could_be name name := by
  sorry

theorem case_sensitive :
  ¬could_be "Carlos Ray" "carlos ray" := by
  sorry
-- </vc-theorems>