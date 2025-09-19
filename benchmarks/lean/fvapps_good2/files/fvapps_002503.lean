-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_palindrome_triangle (n: Nat) : String :=
  sorry

def split_lines (s: String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_triangle_line_count {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  lines.length = n :=
sorry

theorem palindrome_triangle_lines_are_palindromes {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ line ∈ lines, line.data = (line.data.reverse) :=
sorry

theorem palindrome_triangle_lines_increase {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ i, 0 < i → i < lines.length → (lines.get! i).length > (lines.get! (i-1)).length :=
sorry

theorem palindrome_triangle_first_line {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  lines.head! = "1" :=
sorry

theorem palindrome_triangle_only_digits {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ line ∈ lines, ∀ c ∈ line.data, '0' ≤ c ∧ c ≤ '9' :=
sorry

theorem palindrome_triangle_middle_increment {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ i, 0 < i → i < lines.length →
    let line := lines.get! i
    let mid := line.length / 2
    ∀ j, j < mid → line.data[j]! = Char.ofNat ((j + 1) + '0'.toNat) :=
sorry
-- </vc-theorems>