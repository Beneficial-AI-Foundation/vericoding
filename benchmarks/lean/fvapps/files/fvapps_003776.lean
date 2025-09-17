-- <vc-preamble>
def reverse (s : String) : String := sorry

theorem reverse_preserves_length (s : String) :
  (reverse s).length = s.length := sorry

def IsRepeatStart (s : String) (i : String.Pos) : Prop :=
  i = ⟨0⟩ ∨ s.get (String.Pos.mk (i.1 - 1)) = s.get i
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsRepeatEnd (s : String) (i : String.Pos) : Prop :=
  i.1 < s.length - 1 → s.get i = s.get (String.Pos.mk (i.1 + 1))
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_preserves_non_repeats (s : String) (i : String.Pos) : 
  ¬IsRepeatStart s i → ¬IsRepeatEnd s i →
  (reverse s).get i = s.get i := sorry

theorem reverse_swaps_case_on_repeats (s : String) (i : String.Pos) :
  IsRepeatStart s i ∨ IsRepeatEnd s i →
  (reverse s).get i ≠ s.get i := sorry

theorem reverse_idempotent_no_repeats (s : String)
  (h : ∀ i : String.Pos, i.1 < s.length → ¬IsRepeatStart s i ∧ ¬IsRepeatEnd s i) :
  reverse s = s := sorry

theorem reverse_preserves_non_letters (s : String) (i : String.Pos)
  (h : ¬(s.get i).isAlpha) :
  (reverse s).get i = s.get i := sorry

/-
info: 'heLLo world'
-/
-- #guard_msgs in
-- #eval reverse "hello world"

/-
info: 'www'
-/
-- #guard_msgs in
-- #eval reverse "WWW"

/-
info: 'bOOKKEEper'
-/
-- #guard_msgs in
-- #eval reverse "bookkeeper"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded