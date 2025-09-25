-- <vc-preamble>
def Response := String
def Partner := LoveLanguage → Response
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def love_language (p : Partner) (weeks : Nat) : LoveLanguage := sorry

theorem love_language_returns_valid_language 
  (p : Partner) (weeks : Nat) : 
  ∃ (l : LoveLanguage), love_language p weeks = l :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem preferred_language_detected 
  (main_language : LoveLanguage) 
  (p : Partner) 
  (h : ∀ l, p l = if l = main_language then "positive" else "neutral") :
  love_language p 4 = main_language :=
sorry

/-
info: 'words'
-/
-- #guard_msgs in
-- #eval love_language MockPartner("words") 4

/-
info: 'acts'
-/
-- #guard_msgs in
-- #eval love_language MockPartner("acts") 4

/-
info: 'gifts'
-/
-- #guard_msgs in
-- #eval love_language MockPartner("gifts") 4
-- </vc-theorems>