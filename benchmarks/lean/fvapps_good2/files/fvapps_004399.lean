-- <vc-preamble>
def length (s : String) : Nat := s.data.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def automorphic (n : Nat) : String :=
  sorry

def endsWith (s1 s2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem automorphic_returns_valid_string (n : Nat) :
  automorphic n = "Automorphic" ∨ automorphic n = "Not!!" :=
sorry

theorem automorphic_definition (n : Nat) :
  automorphic n = "Automorphic" ↔ endsWith (ToString.toString (n * n)) (ToString.toString n) = true :=
sorry

theorem automorphic_zero_property (n : Nat) :
  n = 0 → automorphic n = "Automorphic" :=
sorry

theorem automorphic_length_property (n : Nat) :
  n > 0 →
  automorphic n = "Automorphic" →
  length (ToString.toString (n * n)) ≥ length (ToString.toString n) :=
sorry
-- </vc-theorems>