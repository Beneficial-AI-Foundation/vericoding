-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rot_energies (B : Float) (Jmin Jmax : Nat) : List Float := sorry

theorem rot_energies_correct_length (B : Float) (J1 J2 : Nat) :
  B > 0 →  
  let Jmin := min J1 J2
  let Jmax := max J1 J2
  List.length (rot_energies B Jmin Jmax) = Jmax - Jmin + 1 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rot_energies_formula (B : Float) (J1 J2 : Nat) (i : Nat) :
  B > 0 →
  let Jmin := min J1 J2
  let Jmax := max J1 J2
  i < List.length (rot_energies B Jmin Jmax) →
  let J := Jmin + i
  Float.abs (List.get! (rot_energies B Jmin Jmax) i - B * (Float.ofNat (J * (J + 1)))) < 1e-10 :=
sorry

theorem negative_B_empty (B : Float) (J1 J2 : Nat) :
  B ≤ 0 →
  rot_energies B (min J1 J2) (max J1 J2) = [] :=
sorry

theorem invalid_J_range_empty (B : Float) (J1 J2 : Nat) :
  B > 0 →
  rot_energies B (max J1 J2 + 1) (min J1 J2) = [] :=
sorry

theorem equal_J_single_value (B : Float) (J : Nat) :
  B > 0 →
  let result := rot_energies B J J
  List.length result = 1 ∧ 
  Float.abs (List.get! result 0 - B * (Float.ofNat (J * (J + 1)))) < 1e-10 :=
sorry
-- </vc-theorems>