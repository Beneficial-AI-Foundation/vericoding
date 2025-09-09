-- <vc-helpers>
-- </vc-helpers>

def roof_fix (new old : List Char) : Bool := sorry

theorem roof_fix_slashes_spaces {new old : List Char} (h : new.length = old.length) :
  roof_fix new old = true →
  ∀ (i : Fin new.length), 
    (old.get ⟨i.val, h ▸ i.isLt⟩ = '\\' ∨ old.get ⟨i.val, h ▸ i.isLt⟩ = '/') →
    new.get i = ' ' :=
sorry

theorem roof_fix_false_case {new old : List Char} (h : new.length = old.length) :
  roof_fix new old = false →
  ∃ (i : Fin new.length),
    (old.get ⟨i.val, h ▸ i.isLt⟩ = '\\' ∨ old.get ⟨i.val, h ▸ i.isLt⟩ = '/') ∧
    new.get i ≠ ' ' :=
sorry

theorem roof_fix_all_spaces_underscores {new old : List Char} 
  (h : new.length = old.length)
  (h_new : ∀ (i : Fin new.length), new.get i = ' ')
  (h_old : ∀ (i : Fin old.length), old.get i = '_') :
  roof_fix new old = true :=
sorry

theorem roof_fix_empty : roof_fix [] [] = true := sorry

theorem roof_fix_singleton_space : 
  roof_fix [' '] ['_'] = true := sorry

theorem roof_fix_double_space :
  roof_fix [' ', ' '] ['_', '_'] = true := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval roof_fix "  l   f l k djmi k" "___\\_____//_____/_"

/-
info: True
-/
-- #guard_msgs in
-- #eval roof_fix "    ikm il  h  llmmc   a i" "__\\_______________________"

/-
info: True
-/
-- #guard_msgs in
-- #eval roof_fix "   h c " "__/____"

-- Apps difficulty: introductory
-- Assurance level: unguarded