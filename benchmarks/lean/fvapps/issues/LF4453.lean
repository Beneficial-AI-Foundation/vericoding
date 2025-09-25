-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_bytes (n : Nat) : List String := sorry

theorem to_bytes_length_correct : ∀ (n : Nat),
  ∀ byte ∈ to_bytes n, String.length byte = 8
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_bytes_valid_bits : ∀ (n : Nat),
  ∀ byte ∈ to_bytes n,
  ∀ c ∈ byte.data,
  c = '0' ∨ c = '1'
  := sorry

theorem to_bytes_roundtrip : ∀ (n : Nat),
  let bytes := to_bytes n
  let recovered := bytes.enum.foldl
    (fun acc (i, byte) => acc + (String.toNat! byte) * (256 ^ (bytes.length - 1 - i)))
    0
  recovered = n
  := sorry

theorem to_bytes_single_byte : ∀ (n : Nat),
  n ≤ 255 →
  (to_bytes n).length = 1
  := sorry

theorem to_bytes_zero :
  to_bytes 0 = ["00000000"]
  := sorry

/-
info: ['00000000']
-/
-- #guard_msgs in
-- #eval to_bytes 0

/-
info: ['00000001']
-/
-- #guard_msgs in
-- #eval to_bytes 1

/-
info: ['00000001', '00000001']
-/
-- #guard_msgs in
-- #eval to_bytes 257
-- </vc-theorems>