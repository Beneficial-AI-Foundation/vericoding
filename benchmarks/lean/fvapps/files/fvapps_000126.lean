-- <vc-preamble>
def makeParens (n : Nat) : String :=
  match n with
  | 0 => ""
  | n+1 => "(" ++ makeParens n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (s : String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_number {n : Int} (h : -1000 ≤ n ∧ n ≤ 1000) :
  calculate s!"{n}" = n :=
sorry

theorem addition {a b : Int} (h : -100 ≤ a ∧ a ≤ 100 ∧ -100 ≤ b ∧ b ≤ 100) :
  calculate s!"{a}+{b}" = a + b :=
sorry

theorem nested_parentheses {n : Int} (h : -50 ≤ n ∧ n ≤ 50) :
  calculate s!"{makeParens n.toNat}1{makeParens n.toNat}" = 1 :=
sorry

theorem parentheses_operations {a b : Int} (h : -50 ≤ a ∧ a ≤ 50 ∧ -50 ≤ b ∧ b ≤ 50) :
  calculate s!"({a})+({b})" = a + b ∧
  calculate s!"({a})-({b})" = a - b :=
sorry

theorem whitespace_invariance (spaces : String) (h : ∀ c ∈ spaces.data, c = ' ') :
  calculate "1+2" = calculate s!"{spaces}1{spaces}+{spaces}2{spaces}" :=
sorry
-- </vc-theorems>