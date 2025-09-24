-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toString (h : String) (m : String) (s : String) : String :=
sorry

def isDigit (s : String) : Bool :=
sorry

def toSeconds (s : String) : Option Nat :=
sorry

def fromNat (n : Nat) : String :=
sorry

def isValidTimeFormat (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_time_conversion
  {h : Nat} {m : Nat} {s : Nat}
  (h_bound : h ≤ 99)
  (m_bound : m ≤ 59)
  (s_bound : s ≤ 59) :
  toSeconds (toString (fromNat h) (fromNat m) (fromNat s)) = some (h * 3600 + m * 60 + s) :=
sorry

theorem invalid_format_returns_none
  (s : String)
  (h_invalid : ¬(isValidTimeFormat s)) :
  toSeconds s = none :=
sorry

theorem invalid_hours
  (h m s : String)
  (h_invalid : h.toNat? = some (Nat.succ 99)) :
  toSeconds (toString h m s) = none :=
sorry

theorem invalid_minutes
  (h m s : String)
  (m_invalid : m.toNat? = some (Nat.succ 59)) :
  toSeconds (toString h m s) = none :=
sorry

theorem invalid_seconds
  (h m s : String)
  (s_invalid : s.toNat? = some (Nat.succ 59)) :
  toSeconds (toString h m s) = none :=
sorry

theorem missing_components_none
  (s : String)
  (h_missing : ¬(isValidTimeFormat s)) :
  toSeconds s = none :=
sorry
-- </vc-theorems>