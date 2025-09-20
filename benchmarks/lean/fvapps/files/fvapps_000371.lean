-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_ip_address (ip: String) : String := sorry

theorem valid_ipv4_gives_ipv4_result
  {ip: String}
  (h_format: ∃ a b c d: Nat, 
    a ≤ 255 ∧ b ≤ 255 ∧ c ≤ 255 ∧ d ≤ 255 ∧
    ip = s!"{a}.{b}.{c}.{d}") :
  validate_ip_address ip = "IPv4" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem neither_when_no_dots_or_colons  
  {ip: String}
  (h_no_delim: '.' ∉ ip.data ∧ ':' ∉ ip.data) :
  validate_ip_address ip = "Neither" := sorry

theorem invalid_ipv4_when_nums_too_large
  {ip: String}
  (h_format: ∃ a b c d: Nat,
    (a > 255 ∨ b > 255 ∨ c > 255 ∨ d > 255) ∧ 
    ip = s!"{a}.{b}.{c}.{d}") :
  validate_ip_address ip = "Neither" := sorry

theorem invalid_ipv6_when_parts_too_long
  {ip: String}
  (h_parts: ∃ parts: List String,
    parts.length = 8 ∧
    (∃ p ∈ parts, p.length > 4) ∧
    ip = String.intercalate ":" parts) :
  validate_ip_address ip = "Neither" := sorry
-- </vc-theorems>