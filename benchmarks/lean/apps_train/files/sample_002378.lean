Given a valid (IPv4) IP address, return a defanged version of that IP address.
A defanged IP address replaces every period "." with "[.]".

Example 1:
Input: address = "1.1.1.1"
Output: "1[.]1[.]1[.]1"
Example 2:
Input: address = "255.100.50.0"
Output: "255[.]100[.]50[.]0"

Constraints:

The given address is a valid IPv4 address.

def defang_ip_addr (s : String) : String := sorry

theorem defang_valid_ip_length {octets : List Nat} 
  (h1 : octets.length = 4)
  (h2 : ∀ x ∈ octets, x ≤ 255) :
  let ip := String.intercalate "." (octets.map toString)
  let defanged := defang_ip_addr ip
  defanged.length = ip.length + 6 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded