-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Char.isAscii (c : Char) : Bool := sorry

def siegfried (week : Nat) (text : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem siegfried_length (week : Nat) (text : String) 
  (h1 : week ≤ 5) (h2 : text.length > 0) : 
  (siegfried week text).length ≤ text.length := sorry

theorem siegfried_consistent (text : String) (h : text.length > 0) :
  siegfried 5 text = siegfried 5 text := sorry

theorem siegfried_idempotent (week : Nat) (text : String) 
  (h1 : week ≤ 5) (h2 : text.length > 0) :
  siegfried week (siegfried week text) = siegfried week text := sorry

theorem siegfried_week_0 (text : String) (h : text.length > 0) :
  siegfried 0 text = text := sorry

theorem siegfried_c_replacement (text : String) 
  (h1 : text.length > 0)
  (h2 : ∀ c ∈ text.data, c = 'c' ∨ c = 'C') :
  let result := siegfried 1 text
  (∀ c ∈ result.data, c.toLower ≠ 'c') ∧
  (∃ c ∈ result.data, c.toLower = 'k') := sorry
-- </vc-theorems>