-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chessboard (n: Nat) (m: Nat) : String :=
sorry

def String.lines (s: String) : List String :=
sorry

def String.characterAt (s: String) (i: Nat) : Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chessboard_empty_for_zero_dims {n m: Nat} :
  (n = 0 ∨ m = 0) → chessboard n m = "" :=
sorry

theorem chessboard_dimensions {n m: Nat} (h1 : n ≠ 0) (h2 : m ≠ 0) :
  let lines := (chessboard n m).lines
  lines.length = n ∧
  ∀ l ∈ lines, l.length = m :=
sorry

theorem chessboard_alternating_pattern {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let lines := (chessboard n m).lines
  ∀ i j, i < n → j < m →
    let line := lines[i]'(by sorry)
    let char := line.characterAt j
    ((i + j) % 2 = 0 → char = '*') ∧
    ((i + j) % 2 ≠ 0 → char = '.') :=
sorry
-- </vc-theorems>