-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ipToInt32 (ip: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ipToInt32_in_range (a b c d: Nat)
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  let result := ipToInt32 ip
  0 ≤ result ∧ result ≤ 4294967295 :=
sorry

theorem ipToInt32_bitwise_composition (a b c d: Nat) 
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  ipToInt32 ip = (a <<< 24) + (b <<< 16) + (c <<< 8) + d :=
sorry

theorem ipToInt32_roundtrip_a (a b c d: Nat)
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  let result := ipToInt32 ip
  a = (result >>> 24) &&& 255 :=
sorry

theorem ipToInt32_roundtrip_b (a b c d: Nat)
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  let result := ipToInt32 ip
  b = (result >>> 16) &&& 255 :=
sorry

theorem ipToInt32_roundtrip_c (a b c d: Nat)
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  let result := ipToInt32 ip
  c = (result >>> 8) &&& 255 :=
sorry

theorem ipToInt32_roundtrip_d (a b c d: Nat)
  (h1: a ≤ 255) (h2: b ≤ 255) (h3: c ≤ 255) (h4: d ≤ 255) :
  let ip := s!"{a}.{b}.{c}.{d}"
  let result := ipToInt32 ip
  d = result &&& 255 :=
sorry
-- </vc-theorems>