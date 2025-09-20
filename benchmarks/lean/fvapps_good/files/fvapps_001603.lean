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
-- </vc-theorems>