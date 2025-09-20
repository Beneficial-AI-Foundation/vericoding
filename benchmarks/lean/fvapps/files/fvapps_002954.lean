-- <vc-preamble>
structure MultiTableOutput where
  lines : List String
  deriving Inhabited
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiTable (n : Nat) : String :=
sorry

def String.count_spaces (s : String) : Nat :=
sorry

def parseMultiTable (s : String) : MultiTableOutput :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multi_table_length (n : Nat) (h : n > 0) :
  (parseMultiTable (multiTable n)).lines.length = 10 :=
sorry

theorem multi_table_format (n : Nat) (h : n > 0) (i : Nat) (h2 : i > 0 ∧ i ≤ 10) :
  let output := parseMultiTable (multiTable n)
  let line := output.lines[i-1]!
  ∃ num1 num2 result : String,
    line = num1 ++ " * " ++ num2 ++ " = " ++ result ∧
    String.toNat! num1 = i ∧
    String.toNat! num2 = n ∧
    String.toNat! result = i * n :=
sorry

theorem multi_table_no_trailing_newline (n : Nat) (h : n > 0) :
  let s := multiTable n
  s.length > 0 ∧ s.data[s.length - 1]! ≠ '\n' :=
sorry

theorem multi_table_spacing (n : Nat) (h : n > 0) (line : String)
  (h2 : line ∈ (parseMultiTable (multiTable n)).lines) :
  line.count_spaces = 4 :=
sorry
-- </vc-theorems>