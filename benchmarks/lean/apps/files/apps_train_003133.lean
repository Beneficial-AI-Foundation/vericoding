-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_in_parts (s : String) (part_length : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_in_parts_max_length {s : String} {part_length : Nat} 
    (h1 : s.length > 0) (h2 : part_length > 0) :
  let parts := (split_in_parts s part_length).split fun c => c = ' '
  ∀ p ∈ parts, p.length ≤ part_length :=
  sorry

theorem split_in_parts_no_change_when_long_enough {s : String} 
    (h : s.length > 0) :
  split_in_parts s s.length = s ∧ 
  split_in_parts s (s.length + 1) = s :=
  sorry

/-
info: 'sup erc ali fra gil ist ice xpi ali doc iou s'
-/
-- #guard_msgs in
-- #eval split_in_parts "supercalifragilisticexpialidocious" 3

/-
info: 'H e l l o K a t a'
-/
-- #guard_msgs in
-- #eval split_in_parts "HelloKata" 1

/-
info: 'HelloKata'
-/
-- #guard_msgs in
-- #eval split_in_parts "HelloKata" 9
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded