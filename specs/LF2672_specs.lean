-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitize (n : Nat) : List Nat :=
  sorry

def digitsToNat (digits : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digitize_single_digits {n : Nat} :
  ∀ d ∈ digitize n, d ≤ 9 := by
  sorry

theorem digitize_length_matches_input {n : Nat} :
  (List.length (digitize n)) = String.length (toString n) := by
  sorry

theorem digitize_reconstruction {n : Nat} :
  n = digitsToNat (List.reverse (digitize n)) := by
  sorry

theorem digitize_preserves_digits {n : Nat} :
  List.map (fun d => toString d) (digitize n) =
  (toString n).toList.map toString := by
  sorry

theorem digitize_zero :
  digitize 0 = [0] := by
  sorry
-- </vc-theorems>