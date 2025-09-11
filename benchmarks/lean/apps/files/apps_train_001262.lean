-- <vc-preamble>
def isString : (s : String) → Bool := sorry
def canReorderString : (s : String) → String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChar (c : Char) (s : String) : Nat := sorry

def isValidLifetime (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem canReorderString_valid_output (s : String) :
  (canReorderString s = "YES") ∨ (canReorderString s = "NO") := sorry

theorem canReorderString_matches_validity (s : String) :
  canReorderString s = (if isValidLifetime s then "YES" else "NO") := sorry

theorem exactly_nine_chars (s : String) (h : s.length = 9) :
  countChar 'L' s ≥ 2 →
  countChar 'T' s ≥ 2 →
  countChar 'I' s ≥ 2 →
  countChar 'M' s ≥ 2 →
  countChar 'E' s ≥ 1 →
  canReorderString s = "YES" := sorry

theorem more_than_nine_chars (s : String) (h : s.length > 9) :
  countChar 'L' s ≥ 2 →
  countChar 'T' s ≥ 2 →
  countChar 'I' s ≥ 2 →
  countChar 'M' s ≥ 2 →
  countChar 'E' s ≥ 2 →
  canReorderString s = "YES" := sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LTIMEAZAZAITLME"

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LLLTTTIIIMMMEEEAHA"

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LTIMEM"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded