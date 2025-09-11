-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitize (n : Nat) : List Nat := sorry 

theorem digitize_length (n : Nat) : 
  List.length (digitize n) = String.length (toString n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digitize_values (n : Nat) :
  ∀ d ∈ digitize n, d ≤ 9 := sorry

theorem digitize_reconstruction (n : Nat) :
  let digits := digitize n
  String.toNat! (String.intercalate "" (List.map toString digits)) = n := sorry

theorem digitize_zero : digitize 0 = [0] := sorry

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval digitize 123

/-
info: [1]
-/
-- #guard_msgs in
-- #eval digitize 1

/-
info: [8, 6, 7, 5, 3, 0, 9]
-/
-- #guard_msgs in
-- #eval digitize 8675309
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible