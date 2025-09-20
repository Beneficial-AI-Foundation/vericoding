-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clock_degree (time: String): String := sorry

theorem valid_time_degree_bounds 
  (h: Nat) (m: Nat) 
  (h_valid: h ≤ 23)
  (m_valid: m ≤ 59)
  (result: String)
  (h_result: result = clock_degree s!"{h}:{m}")
  (h_not_check: result ≠ "Check your time !")
  (hours minutes: String)
  (h_split: result.splitOn ":" = [hours, minutes]): 
  0 ≤ hours.toNat! ∧ hours.toNat! ≤ 360 ∧ 
  0 ≤ minutes.toNat! ∧ minutes.toNat! ≤ 360 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_format_check
  (s: String)
  (h_invalid: ¬s.contains ':' ∨ ¬(s.splitOn ":").all (·.all Char.isDigit)):
  clock_degree s = "Check your time !" := sorry

theorem zero_time:
  clock_degree "00:00" = "360:360" := sorry

theorem hour_conversion_12hr
  (h: Nat) (m: Nat)
  (h_valid: h ≤ 11)
  (m_valid: m ≤ 59)
  (result: String)
  (h_result: result = clock_degree s!"{h}:{m}")
  (hours minutes: Nat)
  (h_split: (result.splitOn ":").map String.toNat! = [hours, minutes]):
  (hours = 360 ∨ hours = h * 30) ∧
  (minutes = 360 ∨ minutes = m * 6) := sorry

theorem hour_conversion_24hr
  (h: Nat) (m: Nat)
  (h_valid: 12 ≤ h ∧ h ≤ 23)
  (m_valid: m ≤ 59)
  (result: String)
  (h_result: result = clock_degree s!"{h}:{m}")
  (hours minutes: Nat)
  (h_split: (result.splitOn ":").map String.toNat! = [hours, minutes]):
  (hours = 360 ∨ hours = (h % 12) * 30) ∧
  (minutes = 360 ∨ minutes = m * 6) := sorry
-- </vc-theorems>