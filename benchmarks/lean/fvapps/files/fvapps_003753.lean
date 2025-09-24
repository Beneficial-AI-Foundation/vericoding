-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Pos2Nat (p : String.Pos) : Nat :=
sorry

def Nat2Pos (n : Nat) : String.Pos :=
sorry

def bracket_pairs (s : String) : Option (List (String.Pos × String.Pos)) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bracket_pairs_valid_indices {s : String} {pairs : List (String.Pos × String.Pos)}
    (h1 : bracket_pairs s = some pairs)
    (open_pos close_pos : String.Pos)
    (h2 : (open_pos, close_pos) ∈ pairs) :
    s.get open_pos = '(' ∧
    s.get close_pos = ')' ∧
    Pos2Nat open_pos < Pos2Nat close_pos :=
sorry

theorem no_brackets_empty_result {s : String} :
  (∀ c, c ∈ s.data → c ≠ '(' ∧ c ≠ ')') →
  bracket_pairs s = some [] :=
sorry

theorem only_closing_brackets_false {s : String} :
  (∀ c, c ∈ s.data → c = ')') →
  s ≠ "" →
  bracket_pairs s = none :=
sorry

theorem only_opening_brackets_false {s : String} :
  (∀ c, c ∈ s.data → c = '(') →
  s ≠ "" →
  bracket_pairs s = none :=
sorry
-- </vc-theorems>