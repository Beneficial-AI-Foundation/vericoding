-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ulam_sequence (u v n: Nat) : List Nat := sorry

theorem ulam_sequence_length {u v n: Nat} (h: u < v):
  (ulam_sequence u v n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ulam_sequence_deterministic {u v n: Nat} (h: u < v):
  ulam_sequence u v n = ulam_sequence u v n := sorry
-- </vc-theorems>