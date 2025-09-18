-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cipher (s : String) : String := sorry

theorem cipher_length_preservation {s : String} :
  s.any (fun c => 97 ≤ c.toNat ∧ c.toNat ≤ 122 ∨ c = ' ') →
  (cipher s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>