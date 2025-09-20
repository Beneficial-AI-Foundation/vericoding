-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String :=
sorry

def lines (s : String) : List String :=
sorry

def reverseString (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_negative_or_zero (n : Int) :
  n ≤ 0 → pattern n = "" :=
sorry

theorem pattern_num_lines (n : Int) :
  n > 0 → (lines (pattern n)).length = 2*n - 1 :=
sorry

theorem pattern_symmetric_lines (n : Int) (i : Nat) :
  n > 0 → i < n-1 →
  (lines (pattern n)).get ⟨i, sorry⟩ = (lines (pattern n)).get ⟨n.toNat * 2 - 2 - i, sorry⟩ :=
sorry

theorem pattern_middle_line_palindrome (n : Int) :
  n > 0 →
  let middle := (lines (pattern n)).get ⟨(n-1).toNat, sorry⟩
  middle = reverseString middle :=
sorry

theorem pattern_middle_line_length (n : Int) :
  n > 0 →
  let middle := (lines (pattern n)).get ⟨(n-1).toNat, sorry⟩
  middle.length = 2*n-1 :=
sorry

theorem pattern_line_length (n : Int) (i : Nat) :
  n > 0 → i < n →
  let line := (lines (pattern n)).get ⟨i, sorry⟩
  line.length = 2*(i+1)-1 + 2*(n.toNat-(i+1)) :=
sorry

theorem pattern_line_palindrome (n : Int) (i : Nat) :
  n > 0 → i < n →
  let line := (lines (pattern n)).get ⟨i, sorry⟩
  line.trim = reverseString (line.trim) :=
sorry
-- </vc-theorems>