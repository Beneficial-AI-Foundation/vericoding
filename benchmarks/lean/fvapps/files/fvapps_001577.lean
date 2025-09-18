-- <vc-preamble>
def middle_permutation (s : String) : String := sorry 

theorem middle_permutation_symmetric (s : String) :
  middle_permutation s = middle_permutation s := by sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def char_list_eq (l1 l2 : List Char) : Prop := 
  ∀ c : Char, c ∈ l1 ↔ c ∈ l2
-- </vc-definitions>

-- <vc-theorems>
theorem middle_permutation_length (s : String) :
  (middle_permutation s).length = s.length := by sorry

theorem middle_permutation_chars (s : String) :
  char_list_eq s.data (middle_permutation s).data := by sorry

theorem middle_permutation_valid (s : String) :
  ∃ perm : List Char, middle_permutation s = String.mk perm ∧
    ∃ (π : List Char → List Char), 
      perm = π s.data ∧
      (∀ (l : List Char), (π l).length = l.length) ∧
      (∀ (l : List Char), char_list_eq (π l) l) := by sorry

/-
info: 'bac'
-/
-- #guard_msgs in
-- #eval middle_permutation "abc"

/-
info: 'bdca'
-/
-- #guard_msgs in
-- #eval middle_permutation "abcd"

/-
info: 'cbxda'
-/
-- #guard_msgs in
-- #eval middle_permutation "abcdx"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded