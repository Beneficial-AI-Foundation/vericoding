-- <vc-preamble>
def simple_transposition (s : String) : String := sorry
def reverse_transposition (s : String) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringTakeEveryNth (s : String) (start : Nat) : String := sorry

theorem length_preserved (s : String) :
  (simple_transposition s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_and_single_char (s : String) :
  s.length ≤ 1 → simple_transposition s = s := sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible