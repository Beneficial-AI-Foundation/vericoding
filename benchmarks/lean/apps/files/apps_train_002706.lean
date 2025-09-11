-- <vc-preamble>
def chessboard (n: Nat) (m: Nat) : String := sorry

def String.lines (s: String) : List String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.characterAt (s: String) (i: Nat) : Char := sorry

theorem chessboard_empty_for_zero_dims {n m: Nat} :
  (n = 0 ∨ m = 0) → chessboard n m = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chessboard_dimensions {n m: Nat} (h1 : n ≠ 0) (h2 : m ≠ 0) :
  let lines := (chessboard n m).lines
  lines.length = n ∧ 
  ∀ l ∈ lines, l.length = m := sorry

theorem chessboard_alternating_pattern {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let lines := (chessboard n m).lines
  ∀ i j, i < n → j < m →
    let line := lines[i]'(by sorry)
    let char := line.characterAt j
    ((i + j) % 2 = 0 → char = '*') ∧
    ((i + j) % 2 ≠ 0 → char = '.') := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval chessboard 0 0

/-
info: '*.\n.*'
-/
-- #guard_msgs in
-- #eval chessboard 2 2

/-
info: expected
-/
-- #guard_msgs in
-- #eval chessboard 8 8
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded