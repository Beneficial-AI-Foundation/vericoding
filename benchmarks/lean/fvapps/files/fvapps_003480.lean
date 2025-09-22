-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mid_endian (n : Nat) : String :=
sorry

def natToHexString (n : Nat) : String :=
sorry

def splitInPairs (s : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mid_endian_idempotent_bytes (n : Nat) :
  let result := mid_endian n
  let pairs := splitInPairs result
  String.join pairs = result :=
sorry

theorem mid_endian_valid_hex (n : Nat) :
  ∃ h, (mid_endian n).toNat? = some h :=
sorry

theorem mid_endian_even_length (n : Nat) :
  (mid_endian n).length % 2 = 0 :=
sorry

theorem mid_endian_sufficient_length (n : Nat) :
  (mid_endian n).length ≥ (natToHexString n).length :=
sorry

theorem mid_endian_hex_chars (n : Nat) :
  ∀ i : Fin (mid_endian n).length,
    (mid_endian n).data.get i ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'] :=
sorry

theorem mid_endian_single_byte (n : Nat) (h : n ≤ 0xFF) :
  mid_endian n = natToHexString n :=
sorry
-- </vc-theorems>