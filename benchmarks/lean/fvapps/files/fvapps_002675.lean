-- <vc-preamble>
def pattern (n : Int) : String := sorry

def String.lines (s : String) : List String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toString (n : Int) : Char := sorry

theorem non_positive_returns_empty
  (n : Int)
  (h : n ≤ 0) :
  pattern n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format_empty
  (n : Int)
  (h : n = 1) :
  pattern n = "" := sorry

theorem output_format_content
  (n : Int) 
  (h1 : n > 1)
  (h2 : n ≤ 100)
  (i : Nat)
  (h3 : i > 0)
  (h4 : i ≤ n/2) :
  (pattern n).lines.get! (i-1) = String.mk (List.replicate (2*i) (toString (2*i))) := sorry

theorem odd_even_equivalence
  (n : Int)
  (h1 : n > 1)
  (h2 : n ≤ 100)
  (h3 : n % 2 = 1) :
  pattern n = pattern (n-1) := sorry

theorem line_count
  (n : Int)
  (h1 : n > 1)
  (h2 : n ≤ 100) :
  (pattern n).lines.length = n/2 := sorry

/-
info: '22\n4444'
-/
-- #guard_msgs in
-- #eval pattern 4

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern 0

/-
info: '22\n4444'
-/
-- #guard_msgs in
-- #eval pattern 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded