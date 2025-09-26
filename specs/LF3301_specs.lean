-- <vc-preamble>
def sort_string (s : String) (ordering : String) : String :=
  sorry

/- Helper function to count occurrences of a character in a string -/

def String.countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

/- Helper function to find first index of character in string -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.findFirstIndex (s : String) (c : Char) : Nat :=
  s.data.indexOf? c |>.getD s.length
-- </vc-definitions>

-- <vc-theorems>
theorem sort_string_length_preservation (s ordering : String) :
  (sort_string s ordering).length = s.length :=
sorry

theorem sort_string_char_preservation (s ordering : String) (c : Char) :
  c ∈ (sort_string s ordering).data → c ∈ s.data :=
sorry

theorem sort_string_frequency_preservation (s ordering : String) (c : Char) :
  (sort_string s ordering).countChar c = s.countChar c :=
sorry

theorem sort_string_ordering_property (s ordering : String) (i j : Char) :
  i ∈ s.data → j ∈ s.data → i ∈ ordering.data → j ∈ ordering.data → 
  ordering.findFirstIndex i < ordering.findFirstIndex j →
  (sort_string s ordering).findFirstIndex i < (sort_string s ordering).findFirstIndex j :=
sorry

theorem sort_string_empty_string (ordering : String) :
  sort_string "" ordering = "" :=
sorry

theorem sort_string_empty_ordering (s : String) :
  sort_string s "" = s :=
sorry

theorem sort_string_idempotent (s ordering : String) :
  sort_string (sort_string s ordering) ordering = sort_string s ordering :=
sorry

/-
info: 'oofs'
-/
-- #guard_msgs in
-- #eval sort_string "foos" "of"

/-
info: 'gnirts'
-/
-- #guard_msgs in
-- #eval sort_string "string" "gnirts"

/-
info: 'aaabnn'
-/
-- #guard_msgs in
-- #eval sort_string "banana" "abn"
-- </vc-theorems>