-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_a_down_arrow_of (n : Nat) : String :=
sorry

def String.lines (s : String) : List String :=
sorry

def String.padLeft (n : Nat) (c : Char) (s : String) : String :=
sorry

def charToNat (c : Char) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrow_length (n : Nat) (h : 0 < n ∧ n ≤ 9) :
  (get_a_down_arrow_of n).lines.length = n :=
sorry

theorem arrow_leading_spaces (n : Nat) (h : 0 < n ∧ n ≤ 9) (i : Nat) (h2 : i < n) :
  let lines := (get_a_down_arrow_of n).lines
  let line := lines[i]!
  (∃ rest : String, line = String.padLeft i ' ' rest) ∧
  line.trim ≠ "" :=
sorry

theorem arrow_decreasing_widths (n : Nat) (h : 0 < n ∧ n ≤ 9) (i : Nat) (h2 : i < n - 1) :
  let lines := (get_a_down_arrow_of n).lines
  lines[i]!.length > lines[i+1]!.length :=
sorry

theorem arrow_line_symmetry (n : Nat) (h : 0 < n ∧ n ≤ 9) (i : Nat) (h2 : i < n) :
  let lines := (get_a_down_arrow_of n).lines
  let stripped := lines[i]!.trim
  let mid := stripped.length / 2
  stripped.take mid = stripped.drop (mid+1) :=
sorry

theorem arrow_sequential_digits (n : Nat) (h : 0 < n ∧ n ≤ 9) (i : Nat) (h2 : i < n) :
  let lines := (get_a_down_arrow_of n).lines
  let digits := lines[i]!.data.filter Char.isDigit
  (∀ d ∈ digits, 0 < charToNat d ∧ charToNat d < 10) ∧
  (digits.length > 1 →
    ∀ j < digits.length/2 - 1,
      charToNat digits[j+1]! - charToNat digits[j]! = 1) :=
sorry
-- </vc-theorems>