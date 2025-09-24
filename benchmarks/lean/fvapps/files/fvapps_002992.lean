-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_utf8_binary (s : String) : String := sorry
def from_utf8_binary (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem utf8_roundtrip (s : String) :
  let binary := to_utf8_binary s
  (∀ c ∈ binary.data, c = '0' ∨ c = '1') ∧
  binary.length % 8 = 0 ∧
  from_utf8_binary binary = s := sorry

theorem single_codepoint_length (n : Nat) (h : n ≤ 0x10FFFF) :
  let s := Char.toString (Char.ofNat n)
  let binary := to_utf8_binary s
  binary.length = 8 ∨ binary.length = 16 ∨ binary.length = 24 ∨ binary.length = 32 := sorry

theorem single_codepoint_roundtrip (n : Nat) (h : n ≤ 0x10FFFF) :
  let s := Char.toString (Char.ofNat n)
  let binary := to_utf8_binary s
  from_utf8_binary binary = s := sorry

theorem empty_strings :
  to_utf8_binary "" = "" ∧
  from_utf8_binary "" = "" := sorry
-- </vc-theorems>