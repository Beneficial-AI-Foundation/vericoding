def simple_transposition (s : String) : String := sorry
def reverse_transposition (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def stringTakeEveryNth (s : String) (start : Nat) : String := sorry

theorem length_preserved (s : String) :
  (simple_transposition s).length = s.length := sorry

theorem empty_and_single_char (s : String) :
  s.length ≤ 1 → simple_transposition s = s := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible