-- <vc-preamble>
def stringRepeat (s : String) (n : Nat) : String :=
  match n with
  | 0 => ""
  | n+1 => s ++ stringRepeat s n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decodeMorse (s : String) : String := sorry

def decodeBits (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dot_timing {unit_time : Nat} (h : 0 < unit_time) (h2 : unit_time ≤ 10) :
  let dot := stringRepeat "1" unit_time
  decodeMorse (decodeBits dot) = "E" :=
sorry

theorem leading_trailing_zeros {zeros : Nat} (h : zeros ≤ 10) :
  let zeros_str := stringRepeat "0" zeros
  decodeMorse (decodeBits (zeros_str ++ "1" ++ zeros_str)) = "E" :=
sorry

theorem spacing {unit_time : Nat} (h : 0 < unit_time) (h2 : unit_time ≤ 5) :
  let dot := stringRepeat "1" unit_time
  let letter_gap := stringRepeat "0" (3 * unit_time)
  let word_gap := stringRepeat "0" (7 * unit_time)
  (decodeMorse (decodeBits (dot ++ letter_gap ++ dot)) = "EE") ∧
  (decodeMorse (decodeBits (dot ++ word_gap ++ dot)) = "E E") :=
sorry

theorem empty_input :
  (decodeBits "" = "") ∧
  (decodeBits "0" = "") ∧
  (decodeBits "000" = "") :=
sorry
-- </vc-theorems>