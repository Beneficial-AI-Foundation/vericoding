-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def segment_cover (A : List Int) (L : Nat) : Nat := sorry

theorem segment_cover_bounds {A : List Int} {L : Nat} (h : A.length > 0) : 
  1 ≤ segment_cover A L ∧ segment_cover A L ≤ A.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem larger_L_needs_fewer_segments {A : List Int} {L : Nat} (h : A.length > 0) (hL : L > 0) :
  segment_cover A L ≤ segment_cover A (L-1) := sorry

theorem ordered_preserves_segments {A B : List Int} {L : Nat} (h : A.length > 0) (h2 : List.Perm A B) :
  segment_cover A L = segment_cover B L := sorry

theorem large_L_single_segment {A : List Int} (h : A.length > 0) :
  let max_dist := (List.maximum? A).getD 0 - (List.minimum? A).getD 0
  segment_cover A ((max_dist : Int).toNat) = 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval segment_cover [1, 3, 4, 5, 8] 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval segment_cover [1, 5, 2, 4, 3] 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval segment_cover [1, 10, 100, 1000] 1
-- </vc-theorems>