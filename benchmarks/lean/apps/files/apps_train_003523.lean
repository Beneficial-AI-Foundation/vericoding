-- <vc-helpers>
-- </vc-helpers>

def ulam_sequence (u v n: Nat) : List Nat := sorry

theorem ulam_sequence_length {u v n: Nat} (h: u < v):
  (ulam_sequence u v n).length = n := sorry

theorem ulam_sequence_deterministic {u v n: Nat} (h: u < v):
  ulam_sequence u v n = ulam_sequence u v n := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible