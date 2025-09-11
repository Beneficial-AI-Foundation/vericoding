-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (s : String) : String := sorry

def is_ascii_letter (c : Char) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_preserves_non_letters (s : String)
  (h : ∀ c, c ∈ s.data → ¬is_ascii_letter c) :
  swap s = s := sorry

theorem swap_changes_ascii_letters (s : String)
  (h : ∀ c, c ∈ s.data → is_ascii_letter c) :
  ∀ i : Fin s.length,
  s.get (String.Pos.mk i) ≠ (swap s).get (String.Pos.mk i) := sorry

theorem swap_preserves_length (s : String) :
  (swap s).length = s.length := sorry

/-
info: 'hELLOwORLD'
-/
-- #guard_msgs in
-- #eval swap "HelloWorld"

/-
info: 'cODEwARS'
-/
-- #guard_msgs in
-- #eval swap "CodeWars"

/-
info: 'tHiS Is a L0ng SentENCE'
-/
-- #guard_msgs in
-- #eval swap "ThIs iS A l0NG sENTence"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded