-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abacaba (n : Nat) : Char := sorry

theorem abacaba_is_lowercase (n : Nat) : 
  let result := abacaba n
  97 ≤ result.toNat ∧ result.toNat ≤ 122 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>