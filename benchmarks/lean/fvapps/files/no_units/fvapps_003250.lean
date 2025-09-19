-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diamond (n : Int) : Option String := sorry

def String.replicate (n : Int) (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_inputs_return_none
  (n : Int)
  (h : n ≤ 0 ∨ n % 2 = 0) :
  diamond n = none :=
sorry

theorem valid_inputs_properties
  (n : Int) 
  (h1 : n > 0)
  (h2 : n % 2 = 1)
  (h3 : n < 101) :
  match diamond n with
  | none => False
  | some result =>
    let lines := String.splitOn result "\n";
    lines.length = n
    ∧ (∀ line ∈ lines, String.length line ≤ n)
    ∧ (∀ line ∈ lines, ∀ c ∈ String.toList line, c = '*' ∨ c = ' ')
    ∧ (∃ line ∈ lines, line = String.replicate n "*") :=
sorry

theorem basic_case :
  diamond 3 = some " *\n***\n *\n" :=
sorry
-- </vc-theorems>