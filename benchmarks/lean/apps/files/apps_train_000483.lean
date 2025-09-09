def longestDecomposition (s : String) : Nat :=
  sorry

def isReversed (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def allCharsSame (s : String) : Bool :=
  sorry

theorem decomposition_length {s : String} (h : s ≠ "") :
  1 ≤ longestDecomposition s ∧ longestDecomposition s ≤ s.length :=
  sorry

theorem concatenated_decomposition {s : String} (h : s ≠ "") :
  longestDecomposition (s ++ s) ≥ 2 * longestDecomposition s :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval longestDecomposition "ghiabcdefhelloadamhelloabcdefghi"

/-
info: 1
-/
-- #guard_msgs in
-- #eval longestDecomposition "merchant"

/-
info: 11
-/
-- #guard_msgs in
-- #eval longestDecomposition "antaprezatepzapreanta"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible