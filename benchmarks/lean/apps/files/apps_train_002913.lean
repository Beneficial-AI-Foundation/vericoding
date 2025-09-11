-- <vc-preamble>
def solve (expr : String) : String := sorry

def isBalanced (expr : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validateResult (result : String) : Bool := sorry

theorem single_variables_theorem (vars : List Char)
  (h1 : ∀ c ∈ vars, 'a' ≤ c ∧ c ≤ 'z')
  (h2 : vars.length ≥ 1)
  (h3 : vars.length ≤ 10) :
  let expr := String.mk vars
  let result := solve expr
  validateResult result ∧ 
  (∀ v ∈ vars, result.data.contains v) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nested_parens_theorem (vars : List Char)
  (h1 : ∀ c ∈ vars, c = 'x' ∨ c = 'y' ∨ c = 'z')
  (h2 : vars.length ≥ 1)
  (h3 : vars.length ≤ 5) :
  let expr := vars.foldl (fun acc v => acc ++ "-(" ++ String.mk [v] ++ ")") (String.mk [vars.head!])
  let result := solve expr
  validateResult result ∧
  (∀ v ∈ vars, result.data.contains v) := sorry

theorem arbitrary_expressions_theorem (expr : String)
  (h1 : expr.length ≥ 1)
  (h2 : expr.length ≤ 20)
  (h3 : ∀ c ∈ expr.data, c = 'x' ∨ c = 'y' ∨ c = 'z' ∨ c = '(' ∨ c = ')' ∨ c = '+' ∨ c = '-')
  (h4 : isBalanced expr) :
  let result := solve expr
  validateResult result ∧
  (∀ c ∈ result.data, c.isAlpha → c ∈ expr.data) := sorry

/-
info: 'x-y-z'
-/
-- #guard_msgs in
-- #eval solve "x-(y+z)"

/-
info: 'x-y+z'
-/
-- #guard_msgs in
-- #eval solve "x-(y-z)"

/-
info: 'u-v+w+x+y-z'
-/
-- #guard_msgs in
-- #eval solve "u-(v-w-(x+y))-z"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded