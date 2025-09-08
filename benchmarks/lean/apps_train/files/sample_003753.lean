/-
Write a function which outputs the positions of matching bracket pairs. The output should be a dictionary with keys the positions of the open brackets '(' and values the corresponding positions of the closing brackets ')'.

For example: input = "(first)and(second)" should return {0:6, 10:17}

If brackets cannot be paired or if the order is invalid (e.g. ')(') return False. In this kata we care only about the positions of round brackets '()', other types of brackets should be ignored.
-/

def Pos2Nat (p : String.Pos) : Nat := sorry
def Nat2Pos (n : Nat) : String.Pos := sorry

-- <vc-helpers>
-- </vc-helpers>

def bracket_pairs (s : String) : Option (List (String.Pos × String.Pos)) := sorry

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

/-
info: {3: 8}
-/
-- #guard_msgs in
-- #eval bracket_pairs "len(list)"

/-
info: {}
-/
-- #guard_msgs in
-- #eval bracket_pairs "string"

/-
info: {0: 9, 2: 4, 6: 7}
-/
-- #guard_msgs in
-- #eval bracket_pairs "(a(b)c()d)"

-- Apps difficulty: introductory
-- Assurance level: unguarded