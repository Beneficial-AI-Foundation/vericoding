-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def date_checker (s : String) : Bool := sorry

def format_date (d m y h min : Nat) : String := 
  toString d ++ "-" ++ toString m ++ "-" ++ toString y ++ " " ++ toString h ++ ":" ++ toString min
-- </vc-definitions>

-- <vc-theorems>
theorem valid_date_format (d m y h min : Nat)  
  (hd : d ≥ 1 ∧ d ≤ 31) 
  (hm : m ≥ 1 ∧ m ≤ 12)
  (hy : y ≤ 9999)
  (hh : h ≤ 23)
  (hmin : min ≤ 59) :
  date_checker (format_date d m y h min) = true := sorry

theorem invalid_date_format (s : String)  
  (h : s.length ≠ 16 ∨ ¬(∃ d m y h min : Nat,
    (d ≥ 1 ∧ d ≤ 31) ∧
    (m ≥ 1 ∧ m ≤ 12) ∧
    (y ≤ 9999) ∧
    (h ≤ 23) ∧
    (min ≤ 59) ∧
    s = format_date d m y h min)) :
  date_checker s = false := sorry
-- </vc-theorems>