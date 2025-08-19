def problem_spec
-- function signature
(impl: Int → Int → Int)
-- inputs
(x y: Int) :=
-- spec
let spec (res: Int) :=
  res - x - y = 0
-- program terminates
∃ result, impl x y = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

def implementation (x y: Int) : Int := x + y

theorem correctness
(x y: Int)
: problem_spec implementation x y  := by
  use (x + y)
  constructor
  · rfl
  · simp [Int.add_sub_cancel]