-- <vc-preamble>
def jumbledString (s : String) (n : Int) : String := sorry

theorem jumbledString_length_preserved (s : String) (n : Int) (h : s.length > 0) :
  (jumbledString s n).length = s.length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSameChars (s₁ s₂ : String) : Prop :=
  ∀ c : Char, (s₁.data.countP (· = c)) = (s₂.data.countP (· = c))
-- </vc-definitions>

-- <vc-theorems>
theorem jumbledString_same_chars (s : String) (n : Int) (h : s.length > 0) :
  isSameChars s (jumbledString s n) := sorry

theorem jumbledString_periodic (s : String) (n : Int) (h : s.length > 0) :
  ∃ k : Nat, k > 0 ∧ 
  jumbledString s n = jumbledString s (n % k) := sorry

theorem jumbledString_empty_or_singleton (s : String) (n : Int) :
  s.length ≤ 1 → jumbledString s n = s := sorry

/-
info: 'Sc o!uhWw'
-/
-- #guard_msgs in
-- #eval jumbled_string "Such Wow!" 1

/-
info: 'bexltept merae'
-/
-- #guard_msgs in
-- #eval jumbled_string "better example" 2

/-
info: 'qtorieuwy'
-/
-- #guard_msgs in
-- #eval jumbled_string "qwertyuio" 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded