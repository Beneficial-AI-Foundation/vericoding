def minInversions (n: Nat) (seq: List Int) : Nat := sorry

def countInversions (seq: List Int) : Nat := sorry

def absInt (i: Int) : Int := 
  if i < 0 then -i else i

-- <vc-helpers>
-- </vc-helpers>

def rangeToInt (n: Nat) : List Int :=
  (List.range n).map Int.ofNat

theorem minInversions_nonnegative (n: Nat) (seq: List Int) : 
  minInversions n seq ≥ 0 := sorry

theorem minInversions_upper_bound (n: Nat) (seq: List Int) :
  minInversions n seq ≤ n * (n-1) / 2 := sorry

theorem minInversions_less_than_original {n: Nat} {seq: List Int} :
  minInversions n seq ≤ countInversions (seq.map absInt) := sorry

theorem binary_sequence_bound {n: Nat} {seq: List Int} 
  (h: ∀ x ∈ seq, x = 0 ∨ x = 1) :
  minInversions n seq ≤ n * n / 4 := sorry

theorem sorted_sequence_zero {n: Nat} :
  minInversions n (rangeToInt n) = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_inversions 2 [2, 1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_inversions 9 [-2, 0, -1, 0, -1, 2, 1, 0, -1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_inversions 9 [0, 0, 1, 1, 0, 0, 1, 0, 1]

-- Apps difficulty: competition
-- Assurance level: unguarded