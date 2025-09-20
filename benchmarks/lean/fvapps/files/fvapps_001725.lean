-- <vc-preamble>
def isOperator (c : Char) : Bool :=
  c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '/' ∨ c = '^'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toPostfix (expr : String) : String := sorry

def isDigit (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def evalStackSize (s : List Char) : Int :=
  s.foldl (fun acc c =>
    if isDigit c then acc + 1
    else if isOperator c then acc - 1
    else acc) 0

theorem toPostfix_only_valid_chars {expr : String} :
  ∀ c, c ∈ (toPostfix expr).data →
    c ∈ expr.data ∨ c.isDigit ∨ c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '/' ∨ c = '^' :=
sorry

theorem toPostfix_no_parens {expr : String} :
  ∀ c, c ∈ (toPostfix expr).data → c ≠ '(' ∧ c ≠ ')' :=
sorry

theorem toPostfix_preserves_operators {expr : String} :
  List.length (List.filter isOperator expr.data) =
  List.length (List.filter isOperator (toPostfix expr).data) :=
sorry

theorem toPostfix_preserves_operands {expr : String} :
  List.length (List.filter isDigit expr.data) =
  List.length (List.filter isDigit (toPostfix expr).data) :=
sorry

theorem toPostfix_final_stack {expr : String} :
  evalStackSize (toPostfix expr).data = 1 :=
sorry

theorem toPostfix_stack_invariant {expr : String} :
  ∀ (n : Nat), n ≤ (toPostfix expr).data.length →
    evalStackSize ((toPostfix expr).data.take n) ≥ 1 :=
sorry
-- </vc-theorems>