-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.toHexString (n: Nat) : String :=
  sorry

def String.trimLeftZeros (s: String) : String :=
  sorry

def hexToDecimal (l: List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hex_to_decimal_length (l: List String) :
  l.length = (hexToDecimal l).length := by
  sorry

theorem hex_to_decimal_non_negative (l: List String) (i: Nat) (h: i < (hexToDecimal l).length) :
  (hexToDecimal l).get ⟨i, h⟩ ≥ 0 := by
  sorry

theorem hex_to_decimal_roundtrip (l: List String) :
  let converted := hexToDecimal l
  let back_to_hex := converted.map Nat.toHexString
  let normalized := l.map String.trimLeftZeros
  back_to_hex = normalized := by
  sorry

theorem hex_to_decimal_increasing (l: List String) (i: Nat) (h₁: i < l.length) (h₂: i < (hexToDecimal l).length) :
  let num := l.get ⟨i, h₁⟩
  num.length > 1 →
  (hexToDecimal l).get ⟨i, h₂⟩ > 0 := by
  sorry
-- </vc-theorems>