-- <vc-helpers>
-- </vc-helpers>

def de_nico (key : String) (msg : String) : String :=
  sorry

theorem de_nico_length_bounded (key : String) (msg : String) :
  (de_nico key msg).length ≤ msg.length := by
  sorry

theorem de_nico_chars_subset (key : String) (msg : String) (c : Char) :
  c ∈ (de_nico key msg).data → c ∈ msg.data := by
  sorry

theorem de_nico_deterministic (key : String) (msg : String) :
  de_nico key msg = de_nico key msg := by
  sorry

theorem de_nico_empty_msg (key : String) :  
  de_nico key "" = "" := by
  sorry

theorem de_nico_no_trailing_spaces (key : String) (msg : String) :
  String.trimRight (de_nico key msg) = de_nico key msg := by
  sorry

/-
info: 'secretinformation'
-/
-- #guard_msgs in
-- #eval de_nico "crazy" "cseerntiofarmit on  "

/-
info: '1234567890'
-/
-- #guard_msgs in
-- #eval de_nico "ba" "2143658709"

/-
info: 'key'
-/
-- #guard_msgs in
-- #eval de_nico "key" "eky"

-- Apps difficulty: introductory
-- Assurance level: unguarded