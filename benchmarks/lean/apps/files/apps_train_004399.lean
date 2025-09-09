def automorphic (n : Nat) : String := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

def length (s : String) : Nat := s.data.length
def endsWith (s1 s2 : String) : Bool := sorry

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

/-
info: 'Automorphic'
-/
-- #guard_msgs in
-- #eval automorphic 6

/-
info: 'Automorphic'
-/
-- #guard_msgs in
-- #eval automorphic 25

/-
info: 'Not!!'
-/
-- #guard_msgs in
-- #eval automorphic 53

-- Apps difficulty: introductory
-- Assurance level: unguarded