-- <vc-preamble>
def countSpaces (s : String) : Nat :=
  sorry

def split (s : String) : List String :=
  sorry

def startsWith (s : String) (c : Char) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reorderSpaces (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reorderSpaces_preserves_spaces (s : String) :
  countSpaces s = countSpaces (reorderSpaces s) := by
  sorry

theorem reorderSpaces_preserves_words (s : String) :
  split s = split (reorderSpaces s) := by
  sorry

theorem reorderSpaces_no_leading_spaces (s : String) :
  ¬startsWith (reorderSpaces s) ' ' := by
  sorry

/-
info: 'this   is   a   sentence'
-/
-- #guard_msgs in
-- #eval reorder_spaces "  this   is  a sentence "

/-
info: 'practice   makes   perfect '
-/
-- #guard_msgs in
-- #eval reorder_spaces " practice   makes   perfect"

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval reorder_spaces "a"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded