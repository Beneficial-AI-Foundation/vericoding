-- <vc-preamble>
def ChessPos := String
def AmazonResult := List Int
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def amazon_check_mate (king : ChessPos) (amazon : ChessPos) : AmazonResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem amazon_check_mate_list_len
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  (amazon_check_mate king amazon).length = 4 :=
  sorry

theorem amazon_check_mate_non_negative
  (king amazon : ChessPos)
  (h : king ≠ amazon)
  (i : Nat)
  (h2 : i < (amazon_check_mate king amazon).length) :
  (amazon_check_mate king amazon).get ⟨i, h2⟩ ≥ 0 :=
  sorry

theorem amazon_check_mate_sum_bound
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  (amazon_check_mate king amazon).foldl (·+·) 0 ≤ 62 :=
  sorry

theorem amazon_check_mate_bounds
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  let result := amazon_check_mate king amazon
  ∀ i : Nat, ∀ h2 : i < result.length,
    0 ≤ result.get ⟨i, h2⟩ ∧
    result.get ⟨i, h2⟩ ≤ 64 :=
  sorry

/-
info: [5, 21, 0, 29]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "d3" "e4"

/-
info: [0, 29, 1, 29]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "a1" "g5"

/-
info: [1, 32, 1, 23]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "a3" "e4"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded