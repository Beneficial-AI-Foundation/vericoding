/-
Write a function to check whether an input string is a valid IPv4 address or IPv6 address or neither.

IPv4 addresses are canonically represented in dot-decimal notation, which consists of four decimal numbers, each ranging from 0 to 255, separated by dots ("."), e.g.,172.16.254.1;

Besides, leading zeros in the IPv4 is invalid. For example, the address 172.16.254.01 is invalid.

IPv6 addresses are represented as eight groups of four hexadecimal digits, each group representing 16 bits. The groups are separated by colons (":"). For example, the address 2001:0db8:85a3:0000:0000:8a2e:0370:7334 is a valid one. Also, we could omit some leading zeros among four hexadecimal digits and some low-case characters in the address to upper-case ones, so 2001:db8:85a3:0:0:8A2E:0370:7334 is also a valid IPv6 address(Omit leading zeros and using upper cases).

However, we don't replace a consecutive group of zero value with a single empty group using two consecutive colons (::) to pursue simplicity. For example, 2001:0db8:85a3::8A2E:0370:7334 is an invalid IPv6 address.

Besides, extra leading zeros in the IPv6 is also invalid. For example, the address 02001:0db8:85a3:0000:0000:8a2e:0370:7334 is invalid.

Note:
You may assume there is no extra space or special characters in the input string.

Example 1:

Input: "172.16.254.1"

Output: "IPv4"

Explanation: This is a valid IPv4 address, return "IPv4".

Example 2:

Input: "2001:0db8:85a3:0:0:8A2E:0370:7334"

Output: "IPv6"

Explanation: This is a valid IPv6 address, return "IPv6".

Example 3:

Input: "256.256.256.256"

Output: "Neither"

Explanation: This is neither a IPv4 address nor a IPv6 address.
-/

-- <vc-helpers>
-- </vc-helpers>

def validate_ip_address (ip: String) : String := sorry

theorem valid_ipv4_gives_ipv4_result
  {ip: String}
  (h_format: ∃ a b c d: Nat, 
    a ≤ 255 ∧ b ≤ 255 ∧ c ≤ 255 ∧ d ≤ 255 ∧
    ip = s!"{a}.{b}.{c}.{d}") :
  validate_ip_address ip = "IPv4" := sorry

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

/-
info: 'IPv4'
-/
-- #guard_msgs in
-- #eval validate_ip_address "172.16.254.1"

/-
info: 'IPv6'
-/
-- #guard_msgs in
-- #eval validate_ip_address "2001:0db8:85a3:0:0:8A2E:0370:7334"

/-
info: 'Neither'
-/
-- #guard_msgs in
-- #eval validate_ip_address "256.256.256.256"

-- Apps difficulty: interview
-- Assurance level: unguarded