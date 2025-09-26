-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stripComments (text : String) (markers : List String) : String := sorry

theorem strip_comments_main_properties (text : String) (markers : List String) :
  let result := stripComments text markers
  -- Result length not greater than input
  (result.length ≤ text.length) ∧
  -- Empty input cases
  (stripComments "" markers = "") ∧
  (stripComments text [] = text) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strip_comments_marker_free (text : String) (markers : List String) :
  let result := stripComments text markers
  -- No marker remains in result
  (∀ m ∈ markers, m ≠ "" → ∀ i : Nat, 
    match result.data[i]?, m.data[0]? with
    | some c1, some c2 => c1 ≠ c2
    | _, _ => true) := sorry

theorem strip_comments_single_char_markers (text : String) (markers : List String) 
  (h : ∀ m ∈ markers, m.length = 1) :
  let result := stripComments text markers
  (∀ i : Nat, 
    match result.data[i]?, text.data[i]? with
    | some c1, some c2 => c1 = c2 ∨ 
        (∃ m ∈ markers, ∃ j < i, 
          text.data[j]? = m.data[0]?)
    | none, _ => true
    | _, none => true) := sorry
-- </vc-theorems>