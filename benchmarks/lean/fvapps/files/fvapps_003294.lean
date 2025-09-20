-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_twos_complement (binary : String) (bits : Nat) : Int :=
sorry

def from_twos_complement (n : Int) (bits : Nat) : String :=
sorry

def removeWhitespace (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem twos_complement_roundtrip (n : Int) (bits : Nat)
  (h1 : bits > 0) (h2 : bits ≤ 64)
  (h3 : n ≥ -(2^(bits-1))) (h4 : n ≤ 2^(bits-1) - 1) :
  to_twos_complement (from_twos_complement n bits) bits = n :=
sorry

theorem binary_roundtrip (binary : String) (bits : Nat)
  (h1 : bits > 0) (h2 : bits ≤ 64)
  (h3 : String.length binary = bits)
  (h4 : ∀ c ∈ binary.data, c = '0' ∨ c = '1') :
  from_twos_complement (to_twos_complement binary bits) bits = binary :=
sorry

theorem bit_length (n : Int) (bits : Nat)
  (h1 : bits > 0) (h2 : bits ≤ 64) :
  String.length (from_twos_complement n bits) = bits ∧
  (∀ c ∈ (from_twos_complement n bits).data, c = '0' ∨ c = '1') :=
sorry

theorem whitespace_handling (binary : String) (bits : Nat)
  (h1 : bits > 0) (h2 : bits ≤ 64)
  (h3 : String.length (removeWhitespace binary) = bits)
  (h4 : ∀ c ∈ (removeWhitespace binary).data, c = '0' ∨ c = '1') :
  to_twos_complement binary bits = to_twos_complement (removeWhitespace binary) bits :=
sorry
-- </vc-theorems>