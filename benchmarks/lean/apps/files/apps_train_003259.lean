-- <vc-helpers>
-- </vc-helpers>

def cipher (s : String) : String := sorry

theorem cipher_length_preservation {s : String} :
  s.any (fun c => 97 ≤ c.toNat ∧ c.toNat ≤ 122 ∨ c = ' ') →
  (cipher s).length = s.length := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible