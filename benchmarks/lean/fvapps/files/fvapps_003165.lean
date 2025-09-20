-- <vc-preamble>
def isDigitChar (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_triangle (m n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem make_triangle_valid_output_type {m n : Nat} :
  ∀ r : String, r = make_triangle m n → (r = "" ∨ String.contains r '\n') :=
sorry

theorem make_triangle_digits_only {m n : Nat} (h : m ≤ n) (h2 : n - m + 1 ≤ 45) :
  ∀ c : Char, c ∈ (make_triangle m n).toList →
    (c = ' ' ∨ c = '\n' ∨ isDigitChar c) :=
sorry

theorem make_triangle_row_growth {m n : Nat} (h : m ≤ n) (h2 : n - m + 1 ≤ 45) :
  let lines := String.split (make_triangle m n) (· = '\n')
  ∀ i : Nat, i < lines.length →
    ∀ h : i < lines.length,
    (String.split (String.trim (lines[i]'h)) (· = ' ')).length = i + 1 :=
sorry

theorem make_triangle_total_elements {m n : Nat} (h : m ≤ n) :
  let size := n - m + 1
  let result := make_triangle m n
  let lines := String.split result (· = '\n')
  result ≠ "" →
  (lines.foldl (fun acc line =>
    acc + (String.split (String.trim line) (· = ' ')).length) 0) = size :=
sorry

theorem make_triangle_invalid_empty {m n : Nat} :
  (m > n ∨ n - m + 1 > 45) → make_triangle m n = "" :=
sorry
-- </vc-theorems>