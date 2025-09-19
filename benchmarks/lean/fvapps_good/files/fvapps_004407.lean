-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numberAndIPaddress (input : String) : String := sorry

theorem ip_to_num_conversion 
  (ip : String) 
  (h1 : ∃ a b c d, a ≥ 0 ∧ a ≤ 255 ∧ 
                   b ≥ 0 ∧ b ≤ 255 ∧
                   c ≥ 0 ∧ c ≤ 255 ∧ 
                   d ≥ 0 ∧ d ≤ 255 ∧
                   ip = s!"{a}.{b}.{c}.{d}") :
  let num := numberAndIPaddress ip
  ∃ n : Nat, 
    n ≤ 4294967295 ∧
    num = toString n ∧
    numberAndIPaddress num = ip := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_to_ip_conversion
  (num : String)
  (h1 : ∃ n : Nat, n ≤ 4294967295 ∧ num = toString n) :
  let ip := numberAndIPaddress num
  ∃ a b c d : Nat,
    a ≤ 255 ∧ b ≤ 255 ∧ c ≤ 255 ∧ d ≤ 255 ∧
    ip = s!"{a}.{b}.{c}.{d}" ∧
    numberAndIPaddress ip = num := sorry

theorem zero_conversions :
  numberAndIPaddress "0.0.0.0" = "0" ∧
  numberAndIPaddress "0" = "0.0.0.0" := sorry
-- </vc-theorems>