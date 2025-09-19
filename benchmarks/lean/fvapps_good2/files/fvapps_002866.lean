-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def simple_transposition (s : String) : String :=
sorry

def reverse_transposition (s : String) : String :=
sorry

def stringTakeEveryNth (s : String) (start : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preserved (s : String) :
  (simple_transposition s).length = s.length :=
sorry

theorem empty_and_single_char (s : String) :
  s.length ≤ 1 → simple_transposition s = s :=
sorry
-- </vc-theorems>