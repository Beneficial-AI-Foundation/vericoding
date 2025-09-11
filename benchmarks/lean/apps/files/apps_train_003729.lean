-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (s : String) : String := sorry

def split (s : String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_preserves_wordcount {s : String} 
  (h : s ≠ "") 
  (h2 : ∀ w ∈ split s, w ≠ "" ∧ w.all (fun c => !c.isWhitespace)) :
  (split (reverse s)).length = (split s).length := sorry

theorem reverse_preserves_words {s : String}
  (h : s ≠ "") 
  (h2 : ∀ w ∈ split s, w ≠ "" ∧ w.all (fun c => !c.isWhitespace)) :
  (split (reverse s)) = (split s) := sorry

theorem reverse_no_leading_whitespace (s : String) :
  ¬(reverse s).startsWith " " := sorry

theorem reverse_no_trailing_whitespace (s : String) :
  ¬(reverse s).endsWith " " := sorry

theorem reverse_empty_stays_empty (s : String) :
  s.trim = "" → reverse s = "" := sorry

/-
info: 'this at expert an am I'
-/
-- #guard_msgs in
-- #eval reverse "I am an expert at this"

/-
info: 'easy so is This'
-/
-- #guard_msgs in
-- #eval reverse "This is so easy"

/-
info: 'cares one no'
-/
-- #guard_msgs in
-- #eval reverse "no one cares"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded