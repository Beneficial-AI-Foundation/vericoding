/-
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
-/

def defang_ip_addr (s : String) : String := sorry

theorem defang_valid_ip_length {octets : List Nat} 
  (h1 : octets.length = 4)
  (h2 : ∀ x ∈ octets, x ≤ 255) :
  let ip := String.intercalate "." (octets.map toString)
  let defanged := defang_ip_addr ip
  defanged.length = ip.length + 6 := sorry

-- <vc-helpers>
-- </vc-helpers>

def countChar (s : String) (c : Char) : Nat :=
  s.toList.filter (· = c) |>.length

theorem defang_valid_ip_reversible {octets : List Nat}
  (h1 : octets.length = 4)
  (h2 : ∀ x ∈ octets, x ≤ 255) :
  let ip := String.intercalate "." (octets.map toString)
  let defanged := defang_ip_addr ip
  String.replace "[.]" "." defanged = ip := sorry

theorem defang_valid_ip_count_dots {octets : List Nat}
  (h1 : octets.length = 4)
  (h2 : ∀ x ∈ octets, x ≤ 255) :
  let ip := String.intercalate "." (octets.map toString)
  let defanged := defang_ip_addr ip 
  countChar defanged '[' = countChar ip '.' := sorry

theorem defang_valid_ip_chars_match {octets : List Nat}
  (h1 : octets.length = 4)
  (h2 : ∀ x ∈ octets, x ≤ 255) :
  let ip := String.intercalate "." (octets.map toString)
  let defanged := defang_ip_addr ip
  let original_chars := ip.toList.filter (· ≠ '.')
  let defanged_chars := defanged.toList.filter (fun c => c ≠ '[' ∧ c ≠ ']' ∧ c ≠ '.')
  original_chars = defanged_chars := sorry

theorem defang_generic_string_length (s : String) :
  let defanged := defang_ip_addr s
  defanged.length = s.length + (2 * countChar s '.') := sorry

theorem defang_generic_string_reversible (s : String) :
  let defanged := defang_ip_addr s
  String.replace "[.]" "." defanged = s := sorry

/-
info: '1[.]1[.]1[.]1'
-/
-- #guard_msgs in
-- #eval defang_ip_addr "1.1.1.1"

/-
info: '255[.]100[.]50[.]0'
-/
-- #guard_msgs in
-- #eval defang_ip_addr "255.100.50.0"

/-
info: '192[.]168[.]1[.]1'
-/
-- #guard_msgs in
-- #eval defang_ip_addr "192.168.1.1"

-- Apps difficulty: introductory
-- Assurance level: unguarded